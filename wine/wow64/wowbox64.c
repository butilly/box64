/*
 * Copyright 2022-2025 André Zwing
 * Copyright 2023 Alexandre Julliard
 */
#include <stddef.h>
#include <stdio.h>
#include <windows.h>
#include <ntstatus.h>
#include <winternl.h>
#include <winnt.h>

#include "debug.h"
#include "os.h"
#include "custommem.h"
#include "dynablock.h"
#include "env.h"
#include "emu/x64emu_private.h"
#include "emu/x87emu_private.h"
#include "x64trace.h"
#include "box64context.h"
#include "box64cpu.h"
#include "box64cpu_util.h"
#include "build_info.h"
#include "rbtree.h"
#include "wine/compiler.h"
#include "wine/debug.h"
#include "hostext.h"
#include "sysinfo.h"
#include "dynarec/arm64/arm64_mapping.h"

uintptr_t box64_pagesize = 4096;

uint32_t default_gs = 0x2b;
uint32_t default_fs = 0;

int box64_rdtsc = 0;
uint8_t box64_rdtsc_shift = 0;
int box64_is32bits = 0;
int box64_unittest_mode = 0;
int box64_wine = 0; // this is for the emulated x86 Wine.
sysinfo_t box64_sysinfo = {0};

static uint32_t x86emu_parity_tab[8] = {
    0x96696996,
    0x69969669,
    0x69969669,
    0x96696996,
    0x69969669,
    0x96696996,
    0x96696996,
    0x69969669,
};

static UINT16 DECLSPEC_ALIGN(4096) bopcode[4096 / sizeof(UINT16)];
static UINT16 DECLSPEC_ALIGN(4096) unxcode[4096 / sizeof(UINT16)];

typedef UINT64 unixlib_handle_t;
NTSTATUS(WINAPI* __wine_unix_call_dispatcher)(unixlib_handle_t, unsigned int, void*);

#define ROUND_ADDR(addr, mask) ((void*)((UINT_PTR)(addr) & ~(UINT_PTR)(mask)))
#define ROUND_SIZE(addr, size) (((SIZE_T)(size) + ((UINT_PTR)(addr) & page_mask) + page_mask) & ~page_mask)
static const UINT_PTR page_mask = 0xfff;

/* reserved TEB64 TLS slots for Wow64
#define WOW64_TLS_CPURESERVED      1
#define WOW64_TLS_TEMPLIST         3
#define WOW64_TLS_USERCALLBACKDATA 5
#define WOW64_TLS_APCLIST          7
#define WOW64_TLS_FILESYSREDIR     8
#define WOW64_TLS_WOW64INFO        10
#define WOW64_TLS_MAX_NUMBER       19
*/
#define WOW64_TLS_ENTRY_CONTEXT (WOW64_TLS_MAX_NUMBER - 1)
#define WOW64_TLS_EMU           (WOW64_TLS_MAX_NUMBER - 2)

int is_addr_unaligned(uintptr_t addr)
{
    // FIXME
    return 0;
}

int is_addr_autosmc(uintptr_t addr)
{
    // FIXME
    return 0;
}

#ifdef DYNAREC
int nUnalignedRange(uintptr_t start, size_t size)
{
    // FIXME
    return 0;
}
void getUnalignedRange(uintptr_t start, size_t size, uintptr_t addrs[])
{
    //FIXME
}
#endif

typedef void (*wrapper_t)(x64emu_t* emu, uintptr_t fnc);
int isSimpleWrapper(wrapper_t fun)
{
    return 0;
}

int isRetX87Wrapper(wrapper_t fun)
{
    return 0;
}

cpu_ext_t cpuext = {0};

static box64context_t box64_context;
box64context_t* my_context = &box64_context;


void fpu_to_box(WOW64_CONTEXT* ctx, x64emu_t* emu)
{
    XMM_SAVE_AREA32* fpu = (XMM_SAVE_AREA32*)ctx->ExtendedRegisters;

    emu->mxcsr.x32 = fpu->MxCsr;
    emu->cw.x16 = fpu->ControlWord;
    emu->sw.x16 = fpu->StatusWord;

    LD2D(&ctx->FloatSave.RegisterArea[0], &emu->x87[0]);
    LD2D(&ctx->FloatSave.RegisterArea[10], &emu->x87[1]);
    LD2D(&ctx->FloatSave.RegisterArea[20], &emu->x87[2]);
    LD2D(&ctx->FloatSave.RegisterArea[30], &emu->x87[3]);
    LD2D(&ctx->FloatSave.RegisterArea[40], &emu->x87[4]);
    LD2D(&ctx->FloatSave.RegisterArea[50], &emu->x87[5]);
    LD2D(&ctx->FloatSave.RegisterArea[60], &emu->x87[6]);
    LD2D(&ctx->FloatSave.RegisterArea[70], &emu->x87[7]);
    memcpy(emu->xmm, fpu->XmmRegisters, sizeof(emu->xmm));
}

void box_to_fpu(WOW64_CONTEXT* ctx, x64emu_t* emu)
{
    XMM_SAVE_AREA32* fpu = (XMM_SAVE_AREA32*)ctx->ExtendedRegisters;

    fpu->MxCsr = emu->mxcsr.x32;
    fpu->ControlWord = emu->cw.x16;
    fpu->StatusWord = emu->sw.x16;

    D2LD(&emu->x87[0], &ctx->FloatSave.RegisterArea[0]);
    D2LD(&emu->x87[1], &ctx->FloatSave.RegisterArea[10]);
    D2LD(&emu->x87[2], &ctx->FloatSave.RegisterArea[20]);
    D2LD(&emu->x87[3], &ctx->FloatSave.RegisterArea[30]);
    D2LD(&emu->x87[4], &ctx->FloatSave.RegisterArea[40]);
    D2LD(&emu->x87[5], &ctx->FloatSave.RegisterArea[50]);
    D2LD(&emu->x87[6], &ctx->FloatSave.RegisterArea[60]);
    D2LD(&emu->x87[7], &ctx->FloatSave.RegisterArea[70]);
    memcpy(fpu->XmmRegisters, emu->xmm, sizeof(emu->xmm));
}

static NTSTATUS invalidate_mapped_section(PVOID addr)
{
    MEMORY_BASIC_INFORMATION mem_info;
    SIZE_T size;
    void* base;

    NTSTATUS ret = NtQueryVirtualMemory(NtCurrentProcess(), addr, MemoryBasicInformation, &mem_info, sizeof(mem_info), NULL);

    if (!NT_SUCCESS(ret))
        return ret;

    base = mem_info.AllocationBase;
    size = (char*)mem_info.BaseAddress + mem_info.RegionSize - (char*)base;

    while (!NtQueryVirtualMemory(NtCurrentProcess(), (char*)base + size, MemoryBasicInformation, &mem_info, sizeof(mem_info), NULL) && mem_info.AllocationBase == base) {
        size += mem_info.RegionSize;
    }

    unprotectDB((uintptr_t)base, (DWORD64)size, 1);
    return STATUS_SUCCESS;
}

void WINAPI BTCpuFlushInstructionCache2(LPCVOID addr, SIZE_T size)
{
    printf_log(LOG_DEBUG, "BTCpuFlushInstructionCache2(%p, %zu)\n", addr, size);
    unprotectDB((uintptr_t)addr, (size_t)size, 1);
}

void WINAPI BTCpuFlushInstructionCacheHeavy(LPCVOID addr, SIZE_T size)
{
    printf_log(LOG_DEBUG, "BTCpuFlushInstructionCacheHeavy(%p, %zu)\n", addr, size);
    unprotectDB((uintptr_t)addr, (size_t)size, 1);
}

void* WINAPI BTCpuGetBopCode(void)
{
    printf_log(LOG_DEBUG, "BTCpuGetBopCode()\n");
    return (UINT32*)&bopcode;
}

void* WINAPI __wine_get_unix_opcode(void)
{
    printf_log(LOG_DEBUG, "__wine_get_unix_opcode()\n");
    return (UINT32*)&unxcode;
}

NTSTATUS WINAPI BTCpuGetContext(HANDLE thread, HANDLE process, void* unknown, WOW64_CONTEXT* ctx)
{
    printf_log(LOG_DEBUG, "BTCpuGetContext(%p, %p, %p, %p)\n", thread, process, unknown, ctx);
    return NtQueryInformationThread(thread, ThreadWow64Context, ctx, sizeof(*ctx), NULL);
}

BOOLEAN WINAPI BTCpuIsProcessorFeaturePresent(UINT feature)
{
    return Box64WineIsProcessorFeaturePresent(feature);
}

void WINAPI BTCpuUpdateProcessorInformation(SYSTEM_CPU_INFORMATION* info)
{
    Box64WineUpdateProcessorInformation(info, PROCESSOR_ARCHITECTURE_INTEL);
}

void WINAPI BTCpuNotifyMemoryDirty(PVOID addr, SIZE_T size)
{
    printf_log(LOG_DEBUG, "BTCpuNotifyMemoryDirty(%p, %zu)\n", addr, size);
    unprotectDB((uintptr_t)addr, (size_t)size, 1);
}

void WINAPI BTCpuNotifyMemoryFree(PVOID addr, SIZE_T size, ULONG free_type)
{
    printf_log(LOG_DEBUG, "BTCpuNotifyMemoryFree(%p, %zu, %u)\n", addr, size, free_type);
    if (!size)
        invalidate_mapped_section(addr);
    else if (free_type & MEM_DECOMMIT)
        unprotectDB((uintptr_t)ROUND_ADDR(addr, page_mask), (DWORD64)ROUND_SIZE(addr, size), 1);
}

void WINAPI BTCpuNotifyMemoryProtect(PVOID addr, SIZE_T size, DWORD new_protect)
{
    printf_log(LOG_DEBUG, "BTCpuNotifyMemoryProtect(%p, %zu, %08x)\n", addr, size, new_protect);
    if (!(new_protect & (PAGE_EXECUTE | PAGE_EXECUTE_READ | PAGE_EXECUTE_READWRITE)))
        return;
    unprotectDB((uintptr_t)addr, size, 1);
}

void WINAPI BTCpuNotifyUnmapViewOfSection(PVOID addr, ULONG flags)
{
    printf_log(LOG_DEBUG, "BTCpuNotifyUnmapViewOfSection(%p, %u)\n", addr, flags);
    invalidate_mapped_section(addr);
}

NTSTATUS WINAPI BTCpuProcessInit(void)
{
    printf_log(LOG_DEBUG, "BTCpuProcessInit()\n");
    HMODULE module;
    UNICODE_STRING str;
    void** p__wine_unix_call_dispatcher;

#define STATIC_ASSERT(COND, MSG) typedef char static_assertion_##MSG[(!!(COND)) * 2 - 1]
    /* otherwise adjust arm64_epilog.S and arm64_next.S */
    STATIC_ASSERT(offsetof(x64emu_t, win64_teb) == 3104, offset_of_b_must_be_4);
#undef STATIC_ASSERT

    LoadEnvVariables();
    InitializeEnvFiles();
    InitializeSystemInfo();

    if (!BOX64ENV(nobanner)) PrintBox64Version(1);
    if (DetectHostCpuFeatures())
        PrintHostCpuFeatures();
    else {
        printf_log(LOG_INFO, "Minimum CPU requirements not met, disabling DynaRec\n");
        SET_BOX64ENV(dynarec, 0);
    }

    TCHAR filename[MAX_PATH];
    if (GetModuleFileNameA(NULL, filename, MAX_PATH)) {
        char* shortname = strrchr(filename, '\\');
        if (shortname) {
            shortname++;
            ApplyEnvFileEntry(shortname);
        }
    }

    PrintEnvVariables(&box64env, LOG_INFO);

    memset(bopcode, 0xc3, sizeof(bopcode));
    memset(unxcode, 0xc3, sizeof(unxcode));
    bopcode[0] = 0x2ecd;
    unxcode[0] = 0x2ecd;

    init_custommem_helper(&box64_context);
    box64_context.db_sizes = rbtree_init("db_sizes");

    if ((ULONG_PTR)bopcode >> 32 || (ULONG_PTR)unxcode >> 32) {
        printf_log(LOG_NONE, "box64cpu loaded above 4G, disabling\n");
        return STATUS_INVALID_ADDRESS;
    }

    RtlInitUnicodeString(&str, L"ntdll.dll");
    LdrGetDllHandle(NULL, 0, &str, &module);
    p__wine_unix_call_dispatcher = RtlFindExportedRoutineByName(module, "__wine_unix_call_dispatcher");
    __wine_unix_call_dispatcher = *p__wine_unix_call_dispatcher;

    RtlInitializeCriticalSection(&box64_context.mutex_dyndump);
    RtlInitializeCriticalSection(&box64_context.mutex_trace);
    RtlInitializeCriticalSection(&box64_context.mutex_tls);
    RtlInitializeCriticalSection(&box64_context.mutex_thread);
    RtlInitializeCriticalSection(&box64_context.mutex_bridge);
    RtlInitializeCriticalSection(&box64_context.mutex_lock);

    InitX64Trace(&box64_context);

    printf_log(LOG_NONE, "WOWBox64 resource diagnostic v2: enabled; fingerprinted lookup sites only\n");

    return STATUS_SUCCESS;
}

static BOOL read_guest_diagnostic(uint32_t addr, void* data, SIZE_T size)
{
    SIZE_T read = 0;
    if (!addr || size > 0x100000000ULL - addr)
        return FALSE;
    return NT_SUCCESS(NtReadVirtualMemory(NtCurrentProcess(), ULongToPtr(addr), data, size, &read)) && read == size;
}

/* Diagnostic for the inspected, relocation-stripped AlanWake.exe only.
 * Never patch guest code or replace the return values being observed. */
int WowResourceTraceSite(uintptr_t pc)
{
    unsigned slot;
    switch (pc) {
    case 0x403527: slot = 0; break; /* cache candidate versus end */
    case 0x403712: slot = 1; break; /* cached payload lookup returned */
    case 0x403761: slot = 2; break; /* loose File::exists returned (AL, not EAX) */
    case 0x403783: slot = 3; break; /* loose payload read returned */
    case 0x40382f: slot = 4; break; /* BaseFile result returned to font loader */
    default:
        return 0;
    }
    IMAGE_DOS_HEADER dos = {0};
    IMAGE_NT_HEADERS32 nt = {0};
    MEMORY_BASIC_INFORMATION info = {0};
    static const unsigned char lookup[] = {0xe8,0x4e,0xfd,0xff,0xff,0x8b,0xf8,0x85,0xff,0x74,0x2e};
    static const unsigned char exists[] = {0xff,0x15,0x50,0x0b,0x63,0x00,0x84,0xc0,0x75,0x07};
    unsigned char code[sizeof(lookup)], fallback[sizeof(exists)];
    unsigned checks = 0;
    if (NT_SUCCESS(NtQueryVirtualMemory(NtCurrentProcess(), (void*)pc, MemoryBasicInformation,
                                       &info, sizeof(info), NULL)) &&
        info.Type == MEM_IMAGE && info.AllocationBase == (void*)0x400000) checks |= 1;
    if (read_guest_diagnostic(0x400000, &dos, sizeof(dos)) && dos.e_magic == IMAGE_DOS_SIGNATURE &&
        dos.e_lfanew >= 0 && dos.e_lfanew <= 0x1000 &&
        read_guest_diagnostic(0x400000 + dos.e_lfanew, &nt, sizeof(nt)) &&
        nt.Signature == IMAGE_NT_SIGNATURE && nt.FileHeader.Machine == IMAGE_FILE_MACHINE_I386)
        checks |= 2;
    if ((checks & 2) && nt.OptionalHeader.SizeOfImage == 0x3a1000 &&
        nt.OptionalHeader.AddressOfEntryPoint == 0x2030f5 && nt.OptionalHeader.CheckSum == 0x2f5f47)
        checks |= 4;
    if (read_guest_diagnostic(0x40370d, code, sizeof(code)) && !memcmp(code, lookup, sizeof(code))) checks |= 8;
    if (read_guest_diagnostic(0x40375b, fallback, sizeof(fallback)) && !memcmp(fallback, exists, sizeof(fallback))) checks |= 16;
    static LONG reported[5];
    if (InterlockedCompareExchange(&reported[slot], 1, 0) == 0)
        printf_log(LOG_NONE, "WOWBox64 resource hook: pc=%08x checks=%02x expected=1f type=%08x base=%p image=%08x entry=%08x checksum=%08x\n",
            (unsigned)pc, checks, (unsigned)info.Type, info.AllocationBase,
            (unsigned)nt.OptionalHeader.SizeOfImage, (unsigned)nt.OptionalHeader.AddressOfEntryPoint,
            (unsigned)nt.OptionalHeader.CheckSum);
    return checks == 31;
}

static int read_resource_name(uint32_t addr, char* name, size_t size)
{
    for (size_t i = 0; i < size; ++i) {
        unsigned char c;
        if (addr > UINT32_MAX - i || !read_guest_diagnostic(addr + i, &c, 1)) return 0;
        name[i] = c;
        if (!c) return 1;
        if (c < 32 || c > 126) return 0;
    }
    return 0;
}

void WowResourceTrace(x64emu_t* emu, uintptr_t pc, int unused)
{
    static LONG captures[5];
    static LONG probes[5];
    unsigned slot;
    uint32_t sp = emu->regs[_SP].dword[0], nameptr = emu->regs[_BX].dword[0];
    uint32_t result = emu->regs[_AX].dword[0], detail = 0;
    char name[160] = {0}, converted[160];
    const char* stage;
    switch (pc) {
    case 0x403527:
        slot = 0; stage = "cache-candidate";
        if (sp > UINT32_MAX - 0x230 || !read_guest_diagnostic(sp + 0x230, &nameptr, 4)) return;
        break;
    case 0x403712: slot = 1; stage = "cache-return"; break;
    case 0x403761: slot = 2; stage = "loose-exists"; result &= 0xff; break;
    case 0x403783: slot = 3; stage = "loose-read"; break;
    case 0x40382f: slot = 4; stage = "file-return"; break;
    default: return;
    }
    int name_readable = read_resource_name(nameptr, name, sizeof(name));
    if (InterlockedIncrement(&probes[slot]) <= 4)
        printf_log(LOG_NONE, "WOWBox64 resource probe: stage=%s pc=%08x nameptr=%08x readable=%d prefix=%.6s result=%08x\n",
            stage, (unsigned)pc, nameptr, name_readable, name_readable ? name : "", result);
    if (!name_readable) return;
    const char* prefix = "fonts/";
    for (unsigned i = 0; i < 6; ++i) {
        unsigned char c = name[i];
        if (c >= 'A' && c <= 'Z') c += 'a' - 'A';
        if (c == '\\') c = '/';
        if (c != prefix[i]) return;
    }
    if (InterlockedIncrement(&captures[slot]) > 32) return;
    printf_log(LOG_NONE, "WOWBox64 resource: stage=%s teb=%p pc=%08x name=%s result=%08x\n",
        stage, NtCurrentTeb(), (unsigned)pc, name, result);
    if (slot == 0) {
        uint32_t entry = emu->regs[_SI].dword[0], fields[3];
        int found = entry != result;
        int readable = found && entry <= UINT32_MAX - 0x120 &&
            read_guest_diagnostic(entry + 0x114, fields, sizeof(fields));
        printf_log(LOG_NONE, "WOWBox64 resource cache: entry=%08x end=%08x found=%d readable=%d ready=%u data=%08x size=%u\n",
            entry, result, found, readable, readable ? fields[0] & 0xff : 0,
            readable ? fields[1] : 0, readable ? fields[2] : 0);
    } else if (slot == 2) {
        if (sp <= UINT32_MAX - 0x14 && read_resource_name(sp + 0x14, converted, sizeof(converted)))
            printf_log(LOG_NONE, "WOWBox64 resource fallback: path=%s exists=%u\n", converted, result);
    } else if (slot == 1 || slot == 3) {
        int readable = sp <= UINT32_MAX - 0xc && read_guest_diagnostic(sp + 0xc, &detail, 4);
        printf_log(LOG_NONE, "WOWBox64 resource payload: size_readable=%d size_raw=%u valid_only_if_result_nonzero=1\n",
            readable, detail);
    }
}

static void log_guest_location(const char* label, unsigned index, uint32_t pc)
{
    MEMORY_BASIC_INFORMATION info;
    if (NT_SUCCESS(NtQueryVirtualMemory(NtCurrentProcess(), ULongToPtr(pc), MemoryBasicInformation,
                                      &info, sizeof(info), NULL)) && info.Type == MEM_IMAGE) {
        printf_log(LOG_NONE, "WOWBox64 guest %s[%u]: pc=%08x image_base=%p rva=%08x executable=%d\n",
            label, index, pc, info.AllocationBase, pc - (uint32_t)(uintptr_t)info.AllocationBase,
            !!(info.Protect & (PAGE_EXECUTE | PAGE_EXECUTE_READ | PAGE_EXECUTE_READWRITE | PAGE_EXECUTE_WRITECOPY)));
    } else {
        printf_log(LOG_NONE, "WOWBox64 guest %s[%u]: pc=%08x (not an image)\n", label, index, pc);
    }
}

static void log_guest_fault(EXCEPTION_RECORD* rec, const CONTEXT* ctx, dynablock_t* db)
{
    static LONG captures;
    if (rec->ExceptionCode != EXCEPTION_ACCESS_VIOLATION || InterlockedIncrement(&captures) > 4)
        return;

    /* The emu spill area can be stale while JIT code is running. Read the
     * fixed guest GPR mapping from the fault context before it is replaced. */
    uint32_t pc = getX64Address(db, (uintptr_t)ctx->Pc);
    uint32_t sp = ctx->X[xRSP], bp = ctx->X[xRBP];
    printf_log(LOG_NONE, "WOWBox64 guest fault: teb=%p host_pc=%p guest_pc=%08x access=%llu address=%p\n",
        NtCurrentTeb(), (void*)(uintptr_t)ctx->Pc, pc,
        rec->NumberParameters >= 1 ? (unsigned long long)rec->ExceptionInformation[0] : ~0ULL,
        rec->NumberParameters >= 2 ? (void*)rec->ExceptionInformation[1] : NULL);
    printf_log(LOG_NONE, "WOWBox64 guest regs: eax=%08x ecx=%08x edx=%08x ebx=%08x esp=%08x ebp=%08x esi=%08x edi=%08x\n",
        (unsigned)ctx->X[xRAX], (unsigned)ctx->X[xRCX], (unsigned)ctx->X[xRDX], (unsigned)ctx->X[xRBX],
        sp, bp, (unsigned)ctx->X[xRSI], (unsigned)ctx->X[xRDI]);
    log_guest_location("fault", 0, pc);

    uint32_t value;
    if (read_guest_diagnostic(ctx->X[xRCX], &value, sizeof(value)))
        printf_log(LOG_NONE, "WOWBox64 guest ecx memory: [%08x]=%08x\n", (unsigned)ctx->X[xRCX], value);
    else
        printf_log(LOG_NONE, "WOWBox64 guest ecx memory: unreadable\n");

    /* Stack words are raw candidates, not an unwound call stack. Reading each
     * word separately also preserves the return address near a guard page. */
    for (unsigned i = 0; i < 16 && (uint64_t)sp + i * 4 <= 0xfffffffcULL; ++i) {
        if (!read_guest_diagnostic(sp + i * 4, &value, sizeof(value))) {
            printf_log(LOG_NONE, "WOWBox64 guest stack: unreadable at word %u\n", i);
            break;
        }
        log_guest_location("stack-word", i, value);
    }
    for (unsigned i = 0; i < 8; ++i) {
        uint32_t frame[2];
        if ((bp & 3) || bp < sp || (uint64_t)bp - sp > 0x100000 ||
            !read_guest_diagnostic(bp, frame, sizeof(frame)))
            break;
        log_guest_location("ebp-return", i, frame[1]);
        if (frame[0] <= bp)
            break;
        bp = frame[0];
    }
}

NTSTATUS WINAPI BTCpuResetToConsistentState(EXCEPTION_POINTERS* ptrs)
{
    printf_log(LOG_DEBUG, "BTCpuResetToConsistentState(%p)\n", ptrs);
    x64emu_t* emu = NtCurrentTeb()->TlsSlots[WOW64_TLS_EMU];
    EXCEPTION_RECORD* rec = ptrs->ExceptionRecord;
    CONTEXT* ctx = ptrs->ContextRecord;

    if (rec->ExceptionCode == EXCEPTION_ACCESS_VIOLATION) {
        dynablock_t* db = NULL;
        void* addr = NULL;
        uint32_t prot;

        if (rec->NumberParameters == 2 && rec->ExceptionInformation[0] == 1)
            addr = ULongToPtr(rec->ExceptionInformation[1]);

        if (addr) {
            unprotectDB((uintptr_t)addr, 1, 1); // unprotect 1 byte... But then, the whole page will be unprotected
            NtContinue(ctx, FALSE);
        }
    }

    /* Pc is a host ARM64 address, not a 32-bit guest pointer. */
    dynablock_t* db = ctx->Pc ? FindDynablockFromNativeAddress((void*)(uintptr_t)ctx->Pc) : NULL;
    static LONG fault_logs;
    if (InterlockedIncrement(&fault_logs) <= 16) {
        printf_log(LOG_NONE, "WOWBox64 host-pc fix: exception=%08x host_pc=%p jit=%d guest_pc=%p\n",
            (unsigned)rec->ExceptionCode, (void*)(uintptr_t)ctx->Pc, !!db,
            db ? (void*)getX64Address(db, (uintptr_t)ctx->Pc) : NULL);
    }
    if (!db)
        return STATUS_SUCCESS;

    log_guest_fault(rec, ctx, db);

    /* Replace the host context with one captured before JIT entry so host code can unwind */
    memcpy(ctx, NtCurrentTeb()->TlsSlots[WOW64_TLS_ENTRY_CONTEXT], sizeof(*ctx));
    return STATUS_SUCCESS;
}

NTSTATUS WINAPI BTCpuSetContext(HANDLE thread, HANDLE process, void* unknown, WOW64_CONTEXT* ctx)
{
    printf_log(LOG_DEBUG, "BTCpuSetContext(%p, %p, %p, %p)\n", thread, process, unknown, ctx);
    return NtSetInformationThread(thread, ThreadWow64Context, ctx, sizeof(*ctx));
}

void WINAPI BTCpuSimulate(void)
{
    printf_log(LOG_DEBUG, "BTCpuSimulate()\n");
    WOW64_CPURESERVED* cpu = NtCurrentTeb()->TlsSlots[WOW64_TLS_CPURESERVED];
    x64emu_t* emu = NtCurrentTeb()->TlsSlots[WOW64_TLS_EMU];
    WOW64_CONTEXT* ctx = (WOW64_CONTEXT*)(cpu + 1);
    CONTEXT entry_context;

    RtlCaptureContext(&entry_context);
    NtCurrentTeb()->TlsSlots[WOW64_TLS_ENTRY_CONTEXT] = &entry_context;

    R_EAX = ctx->Eax;
    R_EBX = ctx->Ebx;
    R_ECX = ctx->Ecx;
    R_EDX = ctx->Edx;
    R_ESI = ctx->Esi;
    R_EDI = ctx->Edi;
    R_EBP = ctx->Ebp;
    R_RIP = ctx->Eip;
    R_ESP = ctx->Esp;
    R_CS = ctx->SegCs & 0xffff;
    R_DS = ctx->SegDs & 0xffff;
    R_ES = ctx->SegEs & 0xffff;
    R_FS = ctx->SegFs & 0xffff;
    R_GS = ctx->SegGs & 0xffff;
    R_SS = ctx->SegSs & 0xffff;
    emu->eflags.x64 = ctx->EFlags;
    emu->segs_offs[_FS] = calculate_fs();
    emu->win64_teb = (uint64_t)NtCurrentTeb();

    fpu_to_box(ctx, emu);

    if (box64env.dynarec)
        DynaRun(emu);
    else
        Run(emu, 0);
}

NTSTATUS WINAPI BTCpuThreadInit(void)
{
    printf_log(LOG_DEBUG, "BTCpuThreadInit()\n");
    WOW64_CONTEXT* ctx;
    x64emu_t* emu = RtlAllocateHeap(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(*emu));

    RtlWow64GetCurrentCpuArea(NULL, (void**)&ctx, NULL);
    emu->context = &box64_context;

    // setup cpu helpers
    for (int i = 0; i < 16; ++i)
        emu->sbiidx[i] = &emu->regs[i];
    emu->sbiidx[4] = &emu->zero;
    emu->x64emu_parity_tab = x86emu_parity_tab;

    reset_fpu(emu);

    NtCurrentTeb()->TlsSlots[WOW64_TLS_EMU] = emu;
    return STATUS_SUCCESS;
}

void EmitInterruptionImpl(x64emu_t* emu, int code)
{
    if (code == 0x2e /* NT syscall */) {
        WOW64_CPURESERVED* cpu = NtCurrentTeb()->TlsSlots[WOW64_TLS_CPURESERVED];
        WOW64_CONTEXT* ctx = (WOW64_CONTEXT*)(cpu + 1);
        int id = R_EAX;
        BOOL is_unix_call = FALSE;

        if (ULongToPtr(R_RIP) == &unxcode)
            is_unix_call = TRUE;
        else if (ULongToPtr(R_RIP) != &bopcode)
            return;

        R_RIP = Pop32(emu);
        ctx->Eip = R_RIP;
        ctx->Esp = R_ESP;
        ctx->Ebx = R_EBX;
        ctx->Esi = R_ESI;
        ctx->Edi = R_EDI;
        ctx->Ebp = R_EBP;
        ctx->EFlags = emu->eflags.x64;
        cpu->Flags = 0;

        box_to_fpu(ctx, emu);

        if (is_unix_call) {
            uintptr_t handle_low = Pop32(emu);
            uintptr_t handle_high = Pop32(emu);
            unsigned int code = Pop32(emu);
            uintptr_t args = Pop32(emu);

            ctx->Esp = R_ESP;
            R_EAX = __wine_unix_call_dispatcher(handle_low | (handle_high << 32), code, (void*)args);
        } else {
            R_EAX = Wow64SystemServiceEx(id, ULongToPtr(ctx->Esp + 4));
        }

        fpu_to_box(ctx, emu);

        R_EBX = ctx->Ebx;
        R_ESI = ctx->Esi;
        R_EDI = ctx->Edi;
        R_EBP = ctx->Ebp;
        R_ESP = ctx->Esp;
        R_RIP = ctx->Eip;
        if (cpu->Flags & WOW64_CPURESERVED_FLAG_RESET_STATE) {
            cpu->Flags &= ~WOW64_CPURESERVED_FLAG_RESET_STATE;
            //R_EAX = ctx->Eax; // do not clobber return value
            R_ECX = ctx->Ecx;
            R_EDX = ctx->Edx;
            R_FS = ctx->SegFs & 0xffff;
            emu->segs_offs[_FS] = calculate_fs();
            emu->eflags.x64 = ctx->EFlags;
        }
    } else {
        RtlRaiseStatus(STATUS_ACCESS_VIOLATION);
    }
}

/* Calls a 2-argument function `Func` setting the parent unwind frame information to the given SP and PC */
static void __attribute__((naked)) SEHFrameTrampoline2Args(void* Arg0, int Arg1, void* Func, uint64_t Sp, uint64_t Pc)
{
    asm(".seh_proc SEHFrameTrampoline2Args\n\t"
        "stp x3, x4, [sp, #-0x10]!\n\t"
        ".seh_pushframe\n\t"
        "stp x29, x30, [sp, #-0x10]!\n\t"
        ".seh_save_fplr_x 16\n\t"
        ".seh_endprologue\n\t"
        "blr x2\n\t"
        "ldp x29, x30, [sp], 0x20\n\t"
        "ret\n\t"
        ".seh_endproc");
}

void EmitInterruption(x64emu_t* emu, int num, void* addr)
{
    CONTEXT* entry_context = NtCurrentTeb()->TlsSlots[WOW64_TLS_ENTRY_CONTEXT];
    SEHFrameTrampoline2Args(emu, num, (void*)EmitInterruptionImpl, entry_context->Sp, entry_context->Pc);
    NtCurrentTeb()->TlsSlots[WOW64_TLS_ENTRY_CONTEXT] = entry_context;
}

NTSTATUS WINAPI LdrDisableThreadCalloutsForDll(HMODULE);

BOOL WINAPI DllMainCRTStartup(HINSTANCE inst, DWORD reason, void* reserved)
{
    if (reason == DLL_PROCESS_ATTACH) LdrDisableThreadCalloutsForDll(inst);
    return TRUE;
}
