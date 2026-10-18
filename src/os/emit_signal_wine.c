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
NTSYSAPI NTSTATUS WINAPI NtReadVirtualMemory(HANDLE, const void*, void*, SIZE_T, SIZE_T*);

/* Record the guest site before RtlRaiseException enters host stack unwinding.
 * A generated-code frame may not be unwindable, so logging in the later
 * WOW64 reset callback is too late. Never dereference the guest PC here. */
static void log_wow64_sigill(x64emu_t* emu, void* addr, int code)
{
    static LONG count;
    MEMORY_BASIC_INFORMATION memory = {0};
    unsigned char bytes[16] = {0};
    char hex[3 * sizeof(bytes) + 1];
    static const char digits[] = "0123456789abcdef";
    SIZE_T read = 0;
    LONG sequence = InterlockedIncrement(&count);
    NTSTATUS query_status, read_status;

    /* Bound output even when the guest deliberately probes unsupported ops. */
    if (sequence < 1 || sequence > 8)
        return;

    query_status = NtQueryVirtualMemory(NtCurrentProcess(), addr,
        MemoryBasicInformation, &memory, sizeof(memory), NULL);
    read_status = NtReadVirtualMemory(NtCurrentProcess(), addr, bytes,
        sizeof(bytes), &read);
    if (read > sizeof(bytes))
        read = sizeof(bytes);
    for (SIZE_T i = 0; i < read; ++i) {
        hex[3 * i] = digits[bytes[i] >> 4];
        hex[3 * i + 1] = digits[bytes[i] & 15];
        hex[3 * i + 2] = ' ';
    }
    hex[3 * read] = 0;

    printf_log(LOG_NONE, "WOW64 guest SIGILL #%ld tid=%d eip=%p addr=%p code=%d "
        "allocation=%p offset=0x%llx type=0x%lx protect=0x%lx query=0x%lx\n",
        sequence, GetTID(), (void*)(uintptr_t)R_RIP, addr, code,
        memory.AllocationBase,
        (unsigned long long)((uintptr_t)addr - (uintptr_t)memory.AllocationBase),
        memory.Type, memory.Protect, (unsigned long)query_status);
    printf_log(LOG_NONE, "WOW64 guest SIGILL #%ld bytes[%zu]=%sread=0x%lx\n",
        sequence, read, hex, (unsigned long)read_status);
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
            printf_log(LOG_DEBUG, "SIGILL at %p with code %d\n", addr, code);
            log_wow64_sigill(emu, addr, code);
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
