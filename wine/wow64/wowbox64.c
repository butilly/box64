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
#include "dynarec/arm64/arm64_mapping.h"
#include "dynarec/arm64/dynarec_arm64_arch.h"
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

NTSTATUS NTAPI NtReadVirtualMemory(HANDLE, PVOID, PVOID, SIZE_T, PSIZE_T);

/* Bounded replacement for the full virtual-memory trace in the affected game.
 * These are notification snapshots, not proof that the operation succeeded. */
static int memory_history_enabled;
static LONG memory_history_lock;
static unsigned memory_history_next, memory_history_count;
static LONG memory_history_skipped, memory_history_reports;
static unsigned memory_history_overwritten;
static struct memory_event {
    const char* operation;
    void* address;
    SIZE_T size;
    ULONG flags;
    NTSTATUS query;
    MEMORY_BASIC_INFORMATION info;
    DWORD tid, eip, esp, stack[8];
    NTSTATUS stack_status;
    SIZE_T stack_bytes;
} memory_history[256];

static void record_memory_event(const char* operation, void* address, SIZE_T size, ULONG flags)
{
    if (!memory_history_enabled || (ULONG_PTR)address > 0xffffffffULL) return;
    if (InterlockedCompareExchange(&memory_history_lock, 1, 0)) {
        InterlockedIncrement(&memory_history_skipped);
        return;
    }
    struct memory_event* event = &memory_history[memory_history_next];
    memset(event, 0, sizeof(*event));
    event->operation = operation;
    event->address = address;
    event->size = size;
    event->flags = flags;
    event->tid = GetTID();
    event->query = NtQueryVirtualMemory(NtCurrentProcess(), address,
        MemoryBasicInformation, &event->info, sizeof(event->info), NULL);
    x64emu_t* emu = NtCurrentTeb()->TlsSlots[WOW64_TLS_EMU];
    if (emu) {
        event->eip = R_RIP;
        event->esp = R_ESP;
        event->stack_status = NtReadVirtualMemory(NtCurrentProcess(), ULongToPtr(R_ESP),
            event->stack, sizeof(event->stack), &event->stack_bytes);
    }
    memory_history_next = (memory_history_next + 1) % 256;
    if (memory_history_count < 256) ++memory_history_count;
    else ++memory_history_overwritten;
    InterlockedExchange(&memory_history_lock, 0);
}

static void log_memory_history(uintptr_t target)
{
    if (!memory_history_enabled || InterlockedIncrement(&memory_history_reports) > 2) return;
    if (InterlockedCompareExchange(&memory_history_lock, 1, 0)) {
        printf_log(LOG_NONE, "WOW64-LIFETIME target=%p history busy\n", (void*)target);
        return;
    }
    unsigned matches = 0;
    printf_log(LOG_NONE, "WOW64-LIFETIME target=%p retained=%u overwritten=%u skipped=%ld newest-first\n",
        (void*)target, memory_history_count, memory_history_overwritten, memory_history_skipped);
    for (unsigned i = 0; i < memory_history_count && matches < 16; ++i) {
        const struct memory_event* event = &memory_history[(memory_history_next + 255 - i) % 256];
        uintptr_t base = (uintptr_t)event->address;
        SIZE_T size = event->size;
        if (!size && NT_SUCCESS(event->query)) {
            base = (uintptr_t)event->info.AllocationBase;
            if (!base) base = (uintptr_t)event->info.BaseAddress;
            size = (uintptr_t)event->info.BaseAddress - base + event->info.RegionSize;
        }
        if (target < base || target - base >= size) continue;
        ++matches;
        printf_log(LOG_NONE, "WOW64-LIFETIME age=%u op=%s addr=%p size=%zu flags=%08lx "
            "query=%08x allocation=%p region=%p region_size=%zu state=%08lx protect=%08lx "
            "tid=%04lx eip=%08lx esp=%08lx stack_status=%08x stack_bytes=%zu "
            "stack=%08lx,%08lx,%08lx,%08lx,%08lx,%08lx,%08lx,%08lx\n",
            i, event->operation, event->address, event->size, event->flags,
            event->query, event->info.AllocationBase, event->info.BaseAddress,
            event->info.RegionSize, event->info.State, event->info.Protect,
            event->tid, event->eip, event->esp, event->stack_status, event->stack_bytes,
            event->stack[0], event->stack[1], event->stack[2], event->stack[3],
            event->stack[4], event->stack[5], event->stack[6], event->stack[7]);
    }
    printf_log(LOG_NONE, "WOW64-LIFETIME matches=%u (notification ranges only)\n", matches);
    InterlockedExchange(&memory_history_lock, 0);
}


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
    record_memory_event("free", addr, size, free_type);
    if (!size)
        invalidate_mapped_section(addr);
    else if (free_type & MEM_DECOMMIT)
        unprotectDB((uintptr_t)ROUND_ADDR(addr, page_mask), (DWORD64)ROUND_SIZE(addr, size), 1);
}

void WINAPI BTCpuNotifyMemoryProtect(PVOID addr, SIZE_T size, DWORD new_protect)
{
    printf_log(LOG_DEBUG, "BTCpuNotifyMemoryProtect(%p, %zu, %08x)\n", addr, size, new_protect);
    record_memory_event("protect", addr, size, new_protect);
    if (!(new_protect & (PAGE_EXECUTE | PAGE_EXECUTE_READ | PAGE_EXECUTE_READWRITE)))
        return;
    unprotectDB((uintptr_t)addr, size, 1);
}

void WINAPI BTCpuNotifyUnmapViewOfSection(PVOID addr, ULONG flags)
{
    printf_log(LOG_DEBUG, "BTCpuNotifyUnmapViewOfSection(%p, %u)\n", addr, flags);
    record_memory_event("unmap", addr, 0, flags);
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
            memory_history_enabled = !_stricmp(shortname, "GOF2.exe");
            if (memory_history_enabled)
                printf_log(LOG_NONE, "WOW64-LIFETIME bounded memory notification history enabled\n");
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

    return STATUS_SUCCESS;
}

/* These reads must not turn an unreadable guest address into a nested fault. */
static void log_fault_bytes(const char* label, uintptr_t address)
{
    unsigned char bytes[32] = {0};
    char hex[sizeof(bytes) * 2 + 1];
    static const char digits[] = "0123456789abcdef";
    SIZE_T count = 0;
    NTSTATUS status = NtReadVirtualMemory(NtCurrentProcess(), (void*)address,
        bytes, sizeof(bytes), &count);
    if (count > sizeof(bytes)) count = sizeof(bytes);
    for (SIZE_T i = 0; i < count; ++i) {
        hex[i * 2] = digits[bytes[i] >> 4];
        hex[i * 2 + 1] = digits[bytes[i] & 15];
    }
    hex[count * 2] = 0;
    printf_log(LOG_NONE, "WOW64 snapshot %s address=%p status=%08x bytes=%zu data=%s\n",
        label, (void*)address, status, count, hex);
}

static void log_fault_context(CONTEXT* ctx)
{
    static LONG active;
    if (InterlockedCompareExchange(&active, 1, 0)) return;

    dynablock_t* db = FindDynablockFromNativeAddress((void*)(ULONG_PTR)ctx->Pc);
    uintptr_t guest_pc = db ? getX64Address(db, ctx->Pc) : 0;
    MEMORY_BASIC_INFORMATION info = {0};
    char module[MAX_PATH] = {0};
    NTSTATUS status = guest_pc ? NtQueryVirtualMemory(NtCurrentProcess(), (void*)guest_pc,
        MemoryBasicInformation, &info, sizeof(info), NULL) : STATUS_INVALID_ADDRESS;
    if (NT_SUCCESS(status) && info.Type == MEM_IMAGE)
        GetModuleFileNameA((HMODULE)info.AllocationBase, module, sizeof(module));
    printf_log(LOG_NONE, "WOW64 snapshot jit=%p mapped_guest_pc=%p query=%08x "
        "guest_base=%p guest_offset=%llx state=%08x protect=%08x type=%08x module=%s\n",
        db, (void*)guest_pc, status, info.AllocationBase,
        NT_SUCCESS(status) ? (unsigned long long)(guest_pc - (uintptr_t)info.AllocationBase) : 0,
        info.State, info.Protect, info.Type, module);

    /* Raw host registers: x10..x17 are live guest GPRs only inside the JIT. */
    for (unsigned i = 0; i < 28; i += 4)
        printf_log(LOG_NONE, "WOW64 snapshot host x%u=%llx x%u=%llx x%u=%llx x%u=%llx\n",
            i, (unsigned long long)ctx->X[i], i + 1, (unsigned long long)ctx->X[i + 1],
            i + 2, (unsigned long long)ctx->X[i + 2], i + 3, (unsigned long long)ctx->X[i + 3]);
    printf_log(LOG_NONE, "WOW64 snapshot host sp=%llx fp=%llx lr=%llx saved_sp=%llx cpsr=%08x\n",
        (unsigned long long)ctx->Sp, (unsigned long long)ctx->Fp,
        (unsigned long long)ctx->Lr, (unsigned long long)ctx->X28, ctx->Cpsr);

    WOW64_CPURESERVED* cpu = NtCurrentTeb()->TlsSlots[WOW64_TLS_CPURESERVED];
    WOW64_CONTEXT guest = {0};
    SIZE_T count = 0;
    status = cpu ? NtReadVirtualMemory(NtCurrentProcess(), cpu + 1,
        &guest, sizeof(guest), &count) : STATUS_INVALID_ADDRESS;
    if (NT_SUCCESS(status) && count == sizeof(guest))
        printf_log(LOG_NONE, "WOW64 snapshot wine eip=%08x esp=%08x eax=%08x ebx=%08x "
            "ecx=%08x edx=%08x esi=%08x edi=%08x ebp=%08x flags=%08x\n",
            guest.Eip, guest.Esp, guest.Eax, guest.Ebx, guest.Ecx, guest.Edx,
            guest.Esi, guest.Edi, guest.Ebp, guest.EFlags);
    else
        printf_log(LOG_NONE, "WOW64 snapshot wine status=%08x bytes=%zu\n", status, count);

    log_fault_bytes("native-code", ctx->Pc);
    if (guest_pc) log_fault_bytes("guest-code", guest_pc);
    if (db && ctx->X14 <= 0xffffffffULL)
        log_fault_bytes("guest-stack", ctx->X14);
    InterlockedExchange(&active, 0);
}

NTSTATUS WINAPI BTCpuResetToConsistentState(EXCEPTION_POINTERS* ptrs)
{
    printf_log(LOG_DEBUG, "BTCpuResetToConsistentState(%p)\n", ptrs);
    x64emu_t* emu = NtCurrentTeb()->TlsSlots[WOW64_TLS_EMU];
    EXCEPTION_RECORD* rec = ptrs->ExceptionRecord;
    CONTEXT* ctx = ptrs->ContextRecord;
    void* native_pc = (void*)(ULONG_PTR)ctx->Pc;
    static LONG fault_log_count;

    /* The normal signal diagnostics are not used by the WOW64 frontend. */
    if (fault_log_count < 8 && InterlockedIncrement(&fault_log_count) <= 8) {
        MEMORY_BASIC_INFORMATION info = {0};
        NTSTATUS status = NtQueryVirtualMemory(NtCurrentProcess(), native_pc,
            MemoryBasicInformation, &info, sizeof(info), NULL);
        printf_log(LOG_NONE, "WOW64 fault code=%08x native_pc=%p exception_addr=%p "
            "cached_guest_pc=%p access=%llu address=%p query=%08x "
            "allocation=%p offset=%llx state=%08x protect=%08x entry_context=%p\n",
            rec->ExceptionCode, native_pc, rec->ExceptionAddress,
            emu ? (void*)(uintptr_t)R_RIP : NULL,
            rec->NumberParameters >= 1 ? (unsigned long long)rec->ExceptionInformation[0] : 0,
            rec->NumberParameters >= 2 ? (void*)(ULONG_PTR)rec->ExceptionInformation[1] : NULL,
            status, info.AllocationBase,
            NT_SUCCESS(status) ? (unsigned long long)((ULONG_PTR)native_pc - (ULONG_PTR)info.AllocationBase) : 0,
            info.State, info.Protect, NtCurrentTeb()->TlsSlots[WOW64_TLS_ENTRY_CONTEXT]);
        log_fault_context(ctx);
    }

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

    /* Native JIT allocations are not limited to the 32-bit guest address space. */
    dynablock_t* db = native_pc ? FindDynablockFromNativeAddress(native_pc) : NULL;
    /* A rejected entry block falls back to Run, whose first opcode load can
     * fault too. Identify that function through its unwind entry, not a build-
     * specific DLL offset, and do not interpret C registers as JIT registers. */
    int interpreter_fetch = 0;
    if (!db && emu && rec->ExceptionCode == EXCEPTION_ACCESS_VIOLATION &&
        rec->NumberParameters == 2 && rec->ExceptionInformation[0] == 0 &&
        rec->ExceptionInformation[1] == R_RIP && emu->old_ip == R_RIP) {
        DWORD64 fault_base = 0, run_base = 0;
        PRUNTIME_FUNCTION fault_fn = RtlLookupFunctionEntry(ctx->Pc, &fault_base, NULL);
        PRUNTIME_FUNCTION run_fn = RtlLookupFunctionEntry((DWORD64)(ULONG_PTR)Run, &run_base, NULL);
        interpreter_fetch = fault_fn && run_fn && fault_base == run_base &&
            fault_fn->BeginAddress == run_fn->BeginAddress;
    }
    if (!db && !interpreter_fetch)
        return STATUS_SUCCESS;

    /* Wine's saved state is from the last syscall, not the faulting instruction.
     * Recover read faults before discarding the live JIT register context. */
    if (emu && rec->ExceptionCode == EXCEPTION_ACCESS_VIOLATION &&
        rec->NumberParameters == 2 && rec->ExceptionInformation[0] == 0) {
        WOW64_CPURESERVED* cpu = NtCurrentTeb()->TlsSlots[WOW64_TLS_CPURESERVED];
        uintptr_t guest_pc = interpreter_fetch ? R_RIP : getX64Address(db, ctx->Pc);
        if (cpu && (guest_pc || interpreter_fetch)) {
            WOW64_CONTEXT* guest = (WOW64_CONTEXT*)(cpu + 1);
            if (!interpreter_fetch) {
                for (unsigned i = 0; i < 16; ++i)
                    emu->regs[i].q[0] = ctx->X[xRAX + i];
                R_RIP = guest_pc;
                emu->eflags.x64 = ctx->X[xFlags];
                adjust_arch(db, emu, ctx, guest_pc);
            }
            if (emu->df) UpdateFlags(emu);
            guest->Eax = R_EAX;
            guest->Ebx = R_EBX;
            guest->Ecx = R_ECX;
            guest->Edx = R_EDX;
            guest->Esi = R_ESI;
            guest->Edi = R_EDI;
            guest->Ebp = R_EBP;
            guest->Esp = R_ESP;
            guest->Eip = R_RIP;
            guest->EFlags = emu->eflags.x64;
            box_to_fpu(guest, emu);
            rec->ExceptionAddress = (void*)guest_pc;
            if (interpreter_fetch) {
                log_memory_history(guest_pc);
                static LONG fetch_stack_reports;
                if (InterlockedIncrement(&fetch_stack_reports) <= 2) {
                    log_fault_bytes("fetch-stack", R_ESP);
                    log_fault_bytes("fetch-frame", R_EBP);
                }
                /* The host read was an x86 instruction fetch, not a data read. */
                rec->ExceptionInformation[0] = 8;
                static LONG fetch_reports;
                if (InterlockedIncrement(&fetch_reports) <= 8)
                    printf_log(LOG_NONE, "WOW64 interpreter fetch delivered eip=%08x esp=%08x\n",
                        guest->Eip, guest->Esp);
            }
        }
    }

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
