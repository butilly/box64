/*
 * Copyright 2022-2025 André Zwing
 * Copyright 2023 Alexandre Julliard
 */
#include <windows.h>
#include <winternl.h>
#include <ntstatus.h>
#include <string.h>
#include <stdint.h>

#include "x64_signals.h"
#include "x64emu.h"
#include "emu/x64emu_private.h"
#include "regs.h"
#include "debug.h"
#include "custommem.h"
#include "wine/compiler.h"
#ifdef BOX64EC
#include "box64ec.h"
#include "os.h"
#include "emu/x64run_private.h"

#endif

#ifndef BOX64EC
/* Capture the guest before RtlRaiseException starts unwinding the host stack.
 * Linux signal diagnostics are not used by the WOW64 frontend. */
static void log_wow64_sigill(x64emu_t* emu, void* addr, int code)
{
    static LONG reports;
    static const char hex[] = "0123456789abcdef";
    MEMORY_BASIC_INFORMATION mbi = {0};
    SIZE_T count = 0;
    NTSTATUS status;
    char bytes[15 * 3 + 1];
    unsigned int n;

    /* CPU-feature probes can intentionally fault: never flood the log. */
    if (InterlockedIncrement(&reports) > 8)
        return;

    printf_log(LOG_NONE, "WOW64-SIGILL guest_ip=%p signal_addr=%p code=%d cs=%04x esp=%08x ebp=%08x\n",
               (void*)(uintptr_t)R_RIP, addr, code, R_CS, R_ESP, R_EBP);
    printf_log(LOG_NONE, "WOW64-SIGILL eax=%08x ebx=%08x ecx=%08x edx=%08x esi=%08x edi=%08x\n",
               R_EAX, R_EBX, R_ECX, R_EDX, R_ESI, R_EDI);

    status = NtQueryVirtualMemory(NtCurrentProcess(), (void*)(uintptr_t)R_RIP,
                                  MemoryBasicInformation, &mbi, sizeof(mbi), &count);
    if (!status)
        printf_log(LOG_NONE, "WOW64-SIGILL allocation_base=%p offset=%p region=%p size=%p protect=%08lx type=%08lx\n",
                   mbi.AllocationBase, (void*)((uintptr_t)R_RIP - (uintptr_t)mbi.AllocationBase),
                   mbi.BaseAddress, (void*)mbi.RegionSize, mbi.Protect, mbi.Type);

    /* Read one byte at a time so a page boundary cannot hide a short opcode.
     * Do not dereference the guest PC: it may itself be invalid. */
    for (n = 0; n < 15; ++n) {
        unsigned char byte;
        count = 0;
        status = NtReadVirtualMemory(NtCurrentProcess(), (void*)((uintptr_t)R_RIP + n),
                                    &byte, sizeof(byte), &count);
        if (status || count != sizeof(byte))
            break;
        bytes[n * 3] = hex[byte >> 4];
        bytes[n * 3 + 1] = hex[byte & 15];
        bytes[n * 3 + 2] = ' ';
    }
    bytes[n * 3] = 0;
    printf_log(LOG_NONE, "WOW64-SIGILL opcode_bytes=%u [%s] read_status=%08lx\n",
               n, bytes, (ULONG)status);
}
#endif

void EmitSignal(x64emu_t* emu, int sig, void* addr, int code)
{
#ifdef BOX64EC
    EXCEPTION_RECORD rec;

    memset(&rec, 0, sizeof(rec));
    rec.ExceptionAddress = addr;

    switch (sig) {
        case X64_SIGILL:
            printf_log(LOG_DEBUG, "box64ec SIGILL at %p code=%d\n", addr, code);
            rec.ExceptionCode = STATUS_ILLEGAL_INSTRUCTION;
            break;
        case X64_SIGSEGV:
            printf_log(LOG_DEBUG, "box64ec SIGSEGV at %p code=0x%x\n", addr, code);
            if (code == 0xbad0 && Box64EC_IsPrivilegedInstruction(addr)) {
                rec.ExceptionCode = STATUS_PRIVILEGED_INSTRUCTION;
                break;
            }
            /* Real AV shape (2 params). Do NOT mark NONCONTINUABLE - that
             * forces Wine into a second-chance path while still on the
             * emulator stack and nests past EmulatorStackBase. */
            rec.ExceptionCode = STATUS_ACCESS_VIOLATION;
            rec.NumberParameters = 2;
            rec.ExceptionInformation[0] = 0; /* read */
            rec.ExceptionInformation[1] = code == 0xbad0
                ? (ULONG_PTR)-1 : (ULONG_PTR)addr;
            break;
        case X64_SIGTRAP:
            printf_log(LOG_DEBUG, "box64ec SIGTRAP at %p code=%d\n", addr, code);
            rec.ExceptionCode = code == 1 ? STATUS_SINGLE_STEP : STATUS_BREAKPOINT;
            if (code == 1)
                emu->eflags.x64 &= ~(1u << 8);
            break;
        default:
            printf_log(LOG_DEBUG, "box64ec unknown signal %d at %p code=%d\n",
                             sig, addr, code);
            rec.ExceptionCode = STATUS_ILLEGAL_INSTRUCTION;
            break;
    }
    Box64EC_RaiseGuestException(&rec);
#else
    EXCEPTION_RECORD rec;

    switch (sig) {
        case X64_SIGILL:
            log_wow64_sigill(emu, addr, code);
            printf_log(LOG_DEBUG, "SIGILL at %p with code %d\n", addr, code);
            rec.ExceptionCode = STATUS_ILLEGAL_INSTRUCTION;
            break;
        case X64_SIGSEGV:
            printf_log(LOG_DEBUG, "SIGSEGV at %p with code %d\n", addr, code);
            rec.ExceptionCode = STATUS_ACCESS_VIOLATION;
            break;
        default:
            printf_log(LOG_INFO, "Warning, unknown signal %d at %p with code %d\n", sig, addr, code);
            rec.ExceptionCode = STATUS_ACCESS_VIOLATION;
            break;
    }
    rec.ExceptionFlags = EXCEPTION_NONCONTINUABLE;
    rec.ExceptionRecord = NULL;
    rec.ExceptionAddress = addr;
    rec.NumberParameters = 0;
    RtlRaiseException(&rec);
#endif
}

void CheckExec(x64emu_t* emu, uintptr_t addr)
{
#ifdef BOX64EC
    /* Hitting ARM64EC DLL code while simulating → leave the interpreter. */
    if (Box64EC_IsEcCode(addr)) {
        printf_log(LOG_DEBUG, "box64ec interpreter-ec-exit addr=%p rip=%p rsp=%p\n",
                    (void*)addr, (void*)(uintptr_t)R_RIP,
                    (void*)(uintptr_t)R_RSP);
        Box64EC_RequestExitToNative(emu, addr);
    }
#else
    (void)emu;
    (void)addr;
#endif
}

void EmitDiv0(x64emu_t* emu, void* addr, int code)
{
#ifdef BOX64EC
    EXCEPTION_RECORD rec;
    (void)emu; (void)code;
    memset(&rec, 0, sizeof(rec));
    printf_log(LOG_DEBUG, "box64ec DIV0 at %p\n", addr);
    rec.ExceptionCode = EXCEPTION_INT_DIVIDE_BY_ZERO;
    rec.ExceptionAddress = addr;
    Box64EC_RaiseGuestException(&rec);
#else
    EXCEPTION_RECORD rec;
    rec.ExceptionCode = EXCEPTION_INT_DIVIDE_BY_ZERO;
    rec.ExceptionFlags = EXCEPTION_NONCONTINUABLE;
    rec.ExceptionRecord = NULL;
    rec.ExceptionAddress = addr;
    rec.NumberParameters = 0;
    RtlRaiseException(&rec);
#endif
}

void EmuInt3(void* opaque, void* addr)
{
#ifdef BOX64EC
    x64emu_t* emu = opaque;
    EXCEPTION_RECORD rec;

    /* The interpreter cursor is past INT3; Wine handlers resume at INT3. */
    R_RIP = *(uintptr_t*)addr - 1;
    memset(&rec, 0, sizeof(rec));
    printf_log(LOG_DEBUG, "box64ec INT3 at %p\n", (void*)(uintptr_t)R_RIP);
    rec.ExceptionCode = STATUS_BREAKPOINT;
    rec.ExceptionAddress = (void*)(uintptr_t)R_RIP;
    rec.NumberParameters = 1;
    Box64EC_RaiseGuestException(&rec);
#else
    EXCEPTION_RECORD rec;

    rec.ExceptionCode = STATUS_BREAKPOINT;
    rec.ExceptionFlags = 0;
    rec.ExceptionRecord = NULL;
    rec.ExceptionAddress = addr;
    rec.NumberParameters = 0;
    RtlRaiseException(&rec);
#endif
}
