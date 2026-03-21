use core::fmt::{write, Write};
use core::mem::offset_of;
use core::ops::RangeBounds;

// Below code is modified from SVSM.
//
// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Nicolai Stange <nstange@suse.de>
use deko_macros::DekoDebug;
use deko_std::address::{VaddrRange, VirtAddr};
use deko_std::array::Array;
use deko_std::cpu::X86GeneralRegs;
use deko_std::deko_rwlock_read_atomic_data;
use deko_std::mem::STACK_SIZE;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::atomic::PAtomicU8;
use vstd::prelude::*;

use crate::cpu::irq::irq_enabled;
use crate::cpu::task::{
    DekoRunQueue, DekoRunQueuePermission, DekoRunnableCtx, X86ExceptionContext, X86InterruptFrame,
};
use crate::cpu::DekoCpuCtx;
use crate::imp::doorbell::HVDoorbell;
use crate::logging::{print_str, CONSOLE, CONSOLE_LOCK};
use crate::mm::DEKO_FRAME_ALLOCATOR_FULL;
use crate::policy::userapp::DEKO_SHADOW_APP_LIST;
use crate::snp::doorbell::HV_DOORBELL_NO_FURTHER_SIGNAL_FLAG;
use crate::snp::vmsa::VMSA;
use crate::snp::{is_vmpl1, GHCB_BUFFER_SIZE};
use crate::{kdebug, kerror, kinfo};

verus! {

extern "C" {
    fn begin_iret_return();
    fn default_iret();
    fn default_return();
    fn return_new_task();
}

#[derive(DekoDebug, Clone, Copy)]
struct StackFrame {
    rbp: VirtAddr,
    rsp: VirtAddr,
    rip: VirtAddr,
    is_aligned: bool,
    is_last: bool,
    is_exception_frame: bool,
    _stack_depth:
        usize,  // Not needed for frame unwinding, only as diagnostic information.
}

#[derive(DekoDebug, Clone, Copy)]
enum UnwoundStackFrame {
    Valid(StackFrame),
    Invalid,
}

type StacksBounds = [VaddrRange; 3];

#[derive(DekoDebug)]
struct StackUnwinder {
    next_frame: Option<UnwoundStackFrame>,
    stacks: StacksBounds,
}

impl StackUnwinder {
    #[verifier::external_body]
    fn new(rbp: VirtAddr, stacks: StacksBounds) -> Self {
        let first_frame = Self::unwind_framepointer_frame(rbp, &stacks);
        Self {
            next_frame: Some(first_frame),
            stacks,
        }
    }

    #[verifier::external_body]
    fn check_unwound_frame(
        rbp: VirtAddr,
        rsp: VirtAddr,
        rip: VirtAddr,
        stacks: &StacksBounds,
    ) -> UnwoundStackFrame {
        // The next frame's rsp or rbp should live on some valid stack,
        // otherwise mark the unwound frame as invalid.
        let Some(stack) = stacks.iter().find(|stack| {
            !stack.is_empty() && (stack.contains(&rsp) || stack.contains(&rbp))
        }) else {
            return UnwoundStackFrame::Invalid;
        };

        // The x86-64 ABI requires stack frames to be 16b-aligned
        let is_aligned = rbp.0 % 16 == 0;
        let is_last = Self::frame_is_last(rbp);
        // let is_exception_frame = is_exception_handler_return_site(rip);

        if !is_last /* && !is_exception_frame */ {
            // Consistency check to ensure forward-progress: never unwind downwards.
            if rbp.0 < rsp.0 {
                return UnwoundStackFrame::Invalid;
            }
        }

        let _stack_depth = (stack.end.0 - rsp.0) as usize;

        UnwoundStackFrame::Valid(StackFrame {
            rbp,
            rsp,
            rip,
            is_aligned,
            is_last,
            // is_exception_frame,
            is_exception_frame: false,
            _stack_depth,
        })
    }

    #[verifier::external_body]
    fn unwind_framepointer_frame(rbp: VirtAddr, stacks: &StacksBounds) -> UnwoundStackFrame {
        let rsp = rbp;

        // Storage for return address + saved %rbp
        let range = rsp..(VirtAddr(rsp.0 + 2 * core::mem::size_of::<VirtAddr>() as u64));

        if !stacks.iter().any(|stack| range.end.0 <= stack.end.0 && range.start.0 >= stack.start.0) {
            return UnwoundStackFrame::Invalid;
        }

        // Saved %rbp
        //
        // SAFETY: This function always works on the stacks of the current
        // context, so de-referencing pointers from the stacks of the context
        // is safe.
        let rbp = unsafe { (rsp.0 as *const VirtAddr).read_unaligned() };
        let rsp = VirtAddr(rsp.0 + core::mem::size_of::<VirtAddr>() as u64);
        // Return address
        //
        // SAFETY: This function always works on the stacks of the current
        // context, so de-referencing pointers from the stacks of the context
        // is safe.
        let rip = unsafe { (rsp.0 as *const VirtAddr).read_unaligned() };
        let rsp = VirtAddr(rsp.0 + core::mem::size_of::<VirtAddr>() as u64);

        Self::check_unwound_frame(rbp, rsp, rip, stacks)
    }

    /// Unwind the stack of the current CPU for debugging purposes.
    #[verifier::external_body]
    pub fn unwind_this_cpu() -> Self {
        let mut rbp: u64;
        // SAFETY: Inline assembly to read RBP, which does not change any state
        // related to memory safety.
        unsafe {
            core::arch::asm!("
                movq %rbp, {}",
                out(reg) rbp,
                options(att_syntax),
            );
        };

        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let cs_stack = match cpu_borrowed.ctx_switch_stack {
            Some( stack) => {
                VirtAddr(stack.0 - STACK_SIZE)..stack
            },
            None => {
                VirtAddr(0)..VirtAddr(0)
            }
        };
        let current_stack = cpu_borrowed.current_stack.clone();
        let df_stack = VirtAddr(0)..VirtAddr(0); // we do not have this.

        Self::new(VirtAddr(rbp), [current_stack, cs_stack, df_stack])
    }
    #[verifier::external_body]
    fn unwind_exception_frame(rsp: VirtAddr, stacks: &StacksBounds) -> UnwoundStackFrame {
        let range = rsp..VirtAddr(rsp.0 + core::mem::size_of::<X86ExceptionContext>() as u64);

        if !stacks.iter().any(|stack| range.end.0 <= stack.end.0 && range.start.0 >= stack.start.0) {
            return UnwoundStackFrame::Invalid;
        }

        // SAFETY: rsp is in a valid memory range as checked previously
        // in this function. It is always properly aligned because
        // X86ExceptionContext is packed(1). It's in the per-CPU stack
        // so no aliasing can occur.
        let ctx = (unsafe { &*(rsp.0 as *const X86ExceptionContext) });
        let rbp = VirtAddr(ctx.regs.rbp);
        let rip = VirtAddr(ctx.frame.rip);
        let rsp = VirtAddr(ctx.frame.rsp);

        Self::check_unwound_frame(rbp, rsp, rip, stacks)
    }

    #[verifier::external_body]
    fn frame_is_last(rbp: VirtAddr) -> bool {
        // A new task is launched with RBP = 0, which is pushed onto the stack
        // immediately and can serve as a marker when the end of the stack has
        // been reached.
        rbp.0 == 0
    }
}

#[verifier::external]
impl Iterator for StackUnwinder {
    type Item = UnwoundStackFrame;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.next_frame;
        match cur {
            Some(cur) => {
                match &cur {
                    UnwoundStackFrame::Invalid => {
                        self.next_frame = None;
                    }
                    UnwoundStackFrame::Valid(cur_frame) => {
                        if cur_frame.is_last {
                            self.next_frame = None
                        } else if cur_frame.is_exception_frame {
                            self.next_frame =
                                Some(Self::unwind_exception_frame(cur_frame.rsp, &self.stacks));
                        } else {
                            self.next_frame =
                                Some(Self::unwind_framepointer_frame(cur_frame.rbp, &self.stacks));
                        }
                    }
                };

                Some(cur)
            }
            None => None,
        }
    }
}

extern "C" {
    static bsp_stack: u8;
    static bsp_stack_end: u8;
}

#[verifier::external_body]
fn print_stack_frame(frame: StackFrame) {
    let mut annotated = false;
    let mut msg = heapless::String::<256>::new();
    msg.write_fmt(format_args!("  [{:016x}]", frame.rip.0)).unwrap();

    if frame.is_exception_frame {
        msg.push_str(" @").unwrap();
        annotated = true;
    }
    if !frame.is_aligned {
        msg.push_str(if annotated { "#" } else { " #" }).unwrap();
    }

    let _ = msg.push_str("\n").unwrap();
    print_str(msg.as_str());
}

#[verifier::external_body]
pub fn print_stack(skip: usize) {
    let unwinder = StackUnwinder::unwind_this_cpu();
    print_str("---BACKTRACE---:\n");

    let guard = CONSOLE_LOCK.acquire_write();

    for frame in unwinder.skip(skip) {
        match frame {
            UnwoundStackFrame::Valid(item) => print_stack_frame(item),
            UnwoundStackFrame::Invalid => print_str("  Invalid frame\n"),
        }
    }
    print_str("---END---\n");

    guard.release_write_no_val();
}

#[verifier::external_body]
pub fn print_stack_raw(addr: u64, n: usize) {
    let data = unsafe { core::slice::from_raw_parts(addr as *const u8, n) };

    kinfo!("stack is", data);
}

#[verifier::external_body]
pub fn debug_doorbell() {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));

    let db_ptr = if !is_vmpl1() {
        cpu_borrowed.doorbell.as_ref().unwrap()
    } else {
        &cpu_borrowed.ext_vmpl1.as_ref().unwrap().doorbell
    };

    let db = deko_rwlock_read_atomic_data! {
        db_ptr,
        db,
        __,
        {
            *db
        }
    };

    let db_bytes = unsafe {
        core::slice::from_raw_parts(db.addr() as *const u8, core::mem::size_of::<HVDoorbell>())
    };

    kinfo!("doorbell is", db_bytes);
}

#[verifier::external_body]
pub fn log_current_doorbell_state(marker: u64) {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let vmpl = if is_vmpl1() { 1u64 } else { 0u64 };

    if is_vmpl1() {
        if let Some(ref ext_vmpl) = cpu_borrowed.ext_vmpl1 {
            deko_rwlock_read_atomic_data! {
                ext_vmpl.doorbell,
                doorbell_ptr,
                doorbell_perm,
                {
                    let doorbell = doorbell_ptr.borrow(Tracked(&doorbell_perm.borrow().ptr_perm));
                    let flags = doorbell.flags.load(Tracked(&doorbell_perm.borrow().hv_perm.flags_perm));
                    let vector = doorbell.vector.load(Tracked(&doorbell_perm.borrow().hv_perm.vector_perm));
                    let pending = (flags & HV_DOORBELL_NO_FURTHER_SIGNAL_FLAG != 0) || (vector != 0);
                    kinfo!(
                        "doorbell_state",
                        "marker", marker => hex,
                        "vmpl", vmpl,
                        "flags", flags as u64 => hex,
                        "vector", vector as u64 => hex,
                        "pending", if pending { "1" } else { "0" }
                    );
                }
            }
        } else {
            kinfo!("doorbell_state", "marker", marker => hex, "vmpl", vmpl, "ext_vmpl1", "none");
        }
    } else {
        if let Some(doorbell_lock) = &cpu_borrowed.doorbell {
            deko_rwlock_read_atomic_data! {
                doorbell_lock,
                doorbell_ptr,
                doorbell_perm,
                {
                    let doorbell = doorbell_ptr.borrow(Tracked(&doorbell_perm.borrow().ptr_perm));
                    let flags = doorbell.flags.load(Tracked(&doorbell_perm.borrow().hv_perm.flags_perm));
                    let vector = doorbell.vector.load(Tracked(&doorbell_perm.borrow().hv_perm.vector_perm));
                    let pending = (flags & HV_DOORBELL_NO_FURTHER_SIGNAL_FLAG != 0) || (vector != 0);
                    kinfo!(
                        "doorbell_state",
                        "marker", marker => hex,
                        "vmpl", vmpl,
                        "flags", flags as u64 => hex,
                        "vector", vector as u64 => hex,
                        "pending", if pending { "1" } else { "0" }
                    );
                }
            }
        } else {
            kinfo!("doorbell_state", "marker", marker => hex, "vmpl", vmpl, "doorbell", "none");
        }
    }
}

#[inline]
#[verifier::external_body]
pub fn hv_trace_event(hv_ptr: DekoPPtr<HVDoorbell>, event: u8, arg0: u64, arg1: u64) {
    const TRACE_EVT_SEQ_OFF: usize = 4;
    const TRACE_EVT_TIMER_HITS_OFF: usize = 5;
    const TRACE_EVT_LAST_VEC_OFF: usize = 6;
    const TRACE_EVT_LAST_FLAGS_OFF: usize = 7;

    unsafe {
        let db_addr = hv_ptr.addr() as usize;
        if db_addr == 0 {
            return ;
        }
        let seq_ptr = (db_addr + TRACE_EVT_SEQ_OFF) as *mut u8;
        let seq = core::ptr::read_volatile(seq_ptr);
        core::ptr::write_volatile(seq_ptr, seq.wrapping_add(1));
        if event == 2 {
            let hits_ptr = (db_addr + TRACE_EVT_TIMER_HITS_OFF) as *mut u8;
            let hits = core::ptr::read_volatile(hits_ptr);
            core::ptr::write_volatile(hits_ptr, hits.wrapping_add(1));
        }
        core::ptr::write_volatile((db_addr + TRACE_EVT_LAST_VEC_OFF) as *mut u8, arg0 as u8);
        core::ptr::write_volatile((db_addr + TRACE_EVT_LAST_FLAGS_OFF) as *mut u8, arg1 as u8);
    }
}

#[verifier::external_body]
#[inline]
pub fn dump_hv_doorbell_trace_and_reset() {
    const TRACE_EVT_SEQ_OFF: usize = 4;
    const TRACE_EVT_TIMER_HITS_OFF: usize = 5;
    const TRACE_EVT_LAST_VEC_OFF: usize = 6;
    const TRACE_EVT_LAST_FLAGS_OFF: usize = 7;
    const TRACE_RESERVED_OFF: usize = 8;
    const TRACE_SLOT0_OFF: usize = TRACE_RESERVED_OFF + 0 * 8;
    const TRACE_SLOT1_OFF: usize = TRACE_RESERVED_OFF + 1 * 8;
    const TRACE_SLOT2_OFF: usize = TRACE_RESERVED_OFF + 2 * 8;
    const TRACE_SLOT3_OFF: usize = TRACE_RESERVED_OFF + 3 * 8;
    const TRACE_SLOT4_OFF: usize = TRACE_RESERVED_OFF + 4 * 8;
    const TRACE_SLOT5_OFF: usize = TRACE_RESERVED_OFF + 5 * 8;
    const TRACE_SLOT6_OFF: usize = TRACE_RESERVED_OFF + 6 * 8;

    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let db_ptr = if !is_vmpl1() {
        cpu_borrowed.doorbell.as_ref()
    } else {
        cpu_borrowed.ext_vmpl1.as_ref().map(|ext| &ext.doorbell)
    };
    let Some(db_ptr) = db_ptr else {
        return ;
    };

    let db_addr = deko_rwlock_read_atomic_data! {
        db_ptr,
        db,
        __,
        {
            db.addr() as usize
        }
    };
    if db_addr == 0 {
        return ;
    }

    unsafe {
        let evt_seq = core::ptr::read_volatile((db_addr + TRACE_EVT_SEQ_OFF) as *const u8);
        let evt_timer_hits = core::ptr::read_volatile((db_addr + TRACE_EVT_TIMER_HITS_OFF) as *const u8);
        let evt_last_vec = core::ptr::read_volatile((db_addr + TRACE_EVT_LAST_VEC_OFF) as *const u8);
        let evt_last_flags = core::ptr::read_volatile((db_addr + TRACE_EVT_LAST_FLAGS_OFF) as *const u8);

        let slot0 = core::ptr::read_volatile((db_addr + TRACE_SLOT0_OFF) as *const u64);
        let slot1 = core::ptr::read_volatile((db_addr + TRACE_SLOT1_OFF) as *const u64);
        if slot0 == 0 && slot1 == 0 && evt_seq == 0 {
            return ;
        }
        let slot2 = core::ptr::read_volatile((db_addr + TRACE_SLOT2_OFF) as *const u64);
        let slot3 = core::ptr::read_volatile((db_addr + TRACE_SLOT3_OFF) as *const u64);
        let slot4 = core::ptr::read_volatile((db_addr + TRACE_SLOT4_OFF) as *const u64);
        let slot5 = core::ptr::read_volatile((db_addr + TRACE_SLOT5_OFF) as *const u64);
        let slot6 = core::ptr::read_volatile((db_addr + TRACE_SLOT6_OFF) as *const u64);

        kinfo!(
            "HV doorbell trace iret_hits=",
            slot0,
            " restart_hits=",
            slot1,
            " iret_frame_rsp=",
            slot2 => hex,
            " iret_frame_rip=",
            slot3 => hex,
        );
        kinfo!(
            "HV doorbell trace restart_old_rsp=",
            slot4 => hex,
            " restart_new_rsp=",
            slot5 => hex,
            " restart_frame_rip=",
            slot6 => hex,
        );
        kinfo!(
            "HV doorbell event seq=",
            evt_seq,
            " timer_hits=",
            evt_timer_hits,
            " last_vec=",
            evt_last_vec,
            " last_flags=",
            evt_last_flags,
        );

        core::ptr::write_volatile((db_addr + TRACE_EVT_SEQ_OFF) as *mut u8, 0);
        core::ptr::write_volatile((db_addr + TRACE_EVT_TIMER_HITS_OFF) as *mut u8, 0);
        core::ptr::write_volatile((db_addr + TRACE_EVT_LAST_VEC_OFF) as *mut u8, 0);
        core::ptr::write_volatile((db_addr + TRACE_EVT_LAST_FLAGS_OFF) as *mut u8, 0);
        core::ptr::write_volatile((db_addr + TRACE_SLOT0_OFF) as *mut u64, 0);
        core::ptr::write_volatile((db_addr + TRACE_SLOT1_OFF) as *mut u64, 0);
        core::ptr::write_volatile((db_addr + TRACE_SLOT2_OFF) as *mut u64, 0);
        core::ptr::write_volatile((db_addr + TRACE_SLOT3_OFF) as *mut u64, 0);
        core::ptr::write_volatile((db_addr + TRACE_SLOT4_OFF) as *mut u64, 0);
        core::ptr::write_volatile((db_addr + TRACE_SLOT5_OFF) as *mut u64, 0);
        core::ptr::write_volatile((db_addr + TRACE_SLOT6_OFF) as *mut u64, 0);
    }
}

#[verifier::external_body]
#[inline]
pub fn dump_vmpl1_doorbell_snapshot_current_cpu() {
    const TRACE_EVT_SEQ_OFF: usize = 4;
    const TRACE_EVT_TIMER_HITS_OFF: usize = 5;
    const TRACE_EVT_LAST_VEC_OFF: usize = 6;
    const TRACE_EVT_LAST_FLAGS_OFF: usize = 7;

    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let ext = match cpu_borrow.ext_vmpl1.as_ref() {
        Some(e) => e,
        None => return ,
    };

    let cpu_id = cpu_borrow.cpu_id;
    let mut db_addr: usize = 0;
    let mut vector: u8 = 0;
    let mut flags: u8 = 0;
    let mut no_eoi: u8 = 0;
    let mut per_vmpl_events: u8 = 0;
    let mut evt_seq: u8 = 0;
    let mut evt_timer_hits: u8 = 0;
    let mut evt_last_vec: u8 = 0;
    let mut evt_last_flags: u8 = 0;

    deko_rwlock_read_atomic_data! {
        &ext.doorbell,
        doorbell_ptr,
        doorbell_perm,
        {
            db_addr = doorbell_ptr.addr() as usize;
            let doorbell = doorbell_ptr.borrow(Tracked(&doorbell_perm.borrow().ptr_perm));
            vector = doorbell.vector.load(Tracked(&doorbell_perm.borrow().hv_perm.vector_perm));
            flags = doorbell.flags.load(Tracked(&doorbell_perm.borrow().hv_perm.flags_perm));
            no_eoi = doorbell.no_eoi_required.load(Tracked(&doorbell_perm.borrow().hv_perm.no_eoi_required_perm));
            per_vmpl_events = doorbell.per_vmpl_events.load(Tracked(&doorbell_perm.borrow().hv_perm.per_vmpl_events_perm));
            unsafe {
                let base = doorbell_ptr.addr() as usize;
                evt_seq = core::ptr::read_volatile((base + TRACE_EVT_SEQ_OFF) as *const u8);
                evt_timer_hits = core::ptr::read_volatile((base + TRACE_EVT_TIMER_HITS_OFF) as *const u8);
                evt_last_vec = core::ptr::read_volatile((base + TRACE_EVT_LAST_VEC_OFF) as *const u8);
                evt_last_flags = core::ptr::read_volatile((base + TRACE_EVT_LAST_FLAGS_OFF) as *const u8);
            }
        }
    }

    kinfo!(
        "VMPL1 doorbell snapshot cpu=",
        cpu_id,
        " db=",
        db_addr => hex,
        " vector=",
        vector,
        " flags=",
        flags,
        " no_eoi=",
        no_eoi,
        " per_vmpl_events=",
        per_vmpl_events,
        " trace_seq=",
        evt_seq,
        " trace_timer_hits=",
        evt_timer_hits,
        " trace_last_vec=",
        evt_last_vec,
        " trace_last_flags=",
        evt_last_flags,
    );
}

#[verifier::external_body]
pub fn log_migrated_runtime_state(tag: &str, vmsa: &VMSA) {
    let rip = unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(vmsa.rip)) };
    let rsp = unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(vmsa.rsp)) };
    let cpl = unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(vmsa.cpl)) };
    let tsc_aux = unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(vmsa.tsc_aux)) };
    let gs_base = unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(vmsa.gs.base)) };
    let kernel_gs_base = unsafe {
        core::ptr::read_unaligned(core::ptr::addr_of!(vmsa.kernel_gs_base))
    };

    kdebug!(
        "migrate_vmsa",
        tag,
        " rip=",
        rip => hex,
        " rsp=",
        rsp => hex,
        " cpl=",
        cpl as u64 => hex,
        " gs=",
        gs_base => hex,
        " kernel_gs=",
        kernel_gs_base => hex,
        " tsc_aux=",
        tsc_aux => hex,
    );

    let start = default_return as *const () as u64;
    let iret_begin = begin_iret_return as *const () as u64;
    let iret_insn = default_iret as *const () as u64;
    let end = return_new_task as *const () as u64;
    if start <= rip && rip < end && rsp != 0 {
        let (frame_rip, frame_cs, frame_rsp, frame_ss, frame_kind) = if rip < iret_begin {
            let ctx = rsp as *const X86ExceptionContext;
            (
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*ctx).frame.rip)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*ctx).frame.cs)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*ctx).frame.rsp)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*ctx).frame.ss)) },
                "exception_ctx",
            )
        } else if rip >= iret_insn {
            let frame = rsp as *const X86InterruptFrame;
            (
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*frame).rip)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*frame).cs)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*frame).rsp)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*frame).ss)) },
                "interrupt_frame",
            )
        } else {
            let ctx = rsp as *const X86ExceptionContext;
            (
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*ctx).frame.rip)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*ctx).frame.cs)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*ctx).frame.rsp)) },
                unsafe { core::ptr::read_unaligned(core::ptr::addr_of!((*ctx).frame.ss)) },
                "exception_ctx_iret_window",
            )
        };

        kdebug!(
            "migrate_vmsa_doorbell_frame",
            tag,
            " kind=",
            frame_kind,
            " frame_rip=",
            frame_rip => hex,
            " frame_cs=",
            frame_cs => hex,
            " frame_rsp=",
            frame_rsp => hex,
            " frame_ss=",
            frame_ss => hex,
        );
    }
}

#[verifier::external_body]
pub fn dump_current_cpu_vmpl1_slot_vmsa() {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let Some(ext_vmpl1) = cpu_borrow.ext_vmpl1.as_ref() else {
        kdebug!("VMPL1 slot VMSA dump skipped: no ext_vmpl1");
        return ;
    };

    let vmsa = unsafe { &*(ext_vmpl1.vmsa.vaddr().0 as *const VMSA) };

    kdebug!("VMPL1 slot VMSA dump before enter: ", vmsa);
}

#[verifier::external_body]
pub fn log_vmpl1_app_binding() {
    let (this_cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = this_cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let cpu_id = cpu_borrow.cpu_id as u32;
    let Some(ext_vmpl1) = cpu_borrow.ext_vmpl1.as_ref() else {
        kdebug!("run_userapp binding: cpu=", cpu_id, " no ext_vmpl1");
        return ;
    };

    let current_pid = ext_vmpl1.current_pid;
    kdebug!(
        "run_userapp slot: cpu=",
        cpu_id,
        " pid=",
        current_pid,
        " slot_dirty=",
        ext_vmpl1.slot_dirty,
        " pending_export_pid=",
        ext_vmpl1.pending_export_pid,
        " pending_export_target_cpu=",
        ext_vmpl1.pending_export_target_cpu,
        " pending_export_version=",
        ext_vmpl1.pending_export_version,
        " last_export_ack_version=",
        ext_vmpl1.last_export_ack_version
    );

    if let Some(pid) = current_pid {
        deko_rwlock_read_atomic_data! {
            DEKO_SHADOW_APP_LIST,
            app_list,
            __,
            {
                if let Some(ref app_list) = app_list {
                    if let Some(app) = app_list.get(&pid) {
                        kdebug!(
                            "run_userapp app: pid=",
                            pid,
                            " owner_cpu=",
                            app.ext.owner_cpu,
                            " loaded_cpu=",
                            app.ext.loaded_cpu,
                            " state_version=",
                            app.ext.state_version,
                            " migration_state=",
                            app.ext.migration_state,
                            " state=",
                            app.ext.state
                        );
                    } else {
                        kdebug!("run_userapp app: pid=", pid, " missing from shadow app list");
                    }
                } else {
                    kdebug!("run_userapp app: shadow app list not initialized");
                }
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn log_nested_irq_state(marker: u64) {
    let cur_vmpl1 = is_vmpl1();
    let if_enabled = irq_enabled();

    let (this_cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut cpu_taken = this_cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    let vmpl0_count;
    proof_with!(Tracked(&mut cpu_perm.irq_state_perm));
    let tracked mut vmpl0_count_perm = cpu_perm.irq_state_perm.counts_perm.tracked_remove(0);
    vmpl0_count = cpu_taken.nested_irq.counts[0].load(Tracked(&mut vmpl0_count_perm));
    proof {
        cpu_perm.irq_state_perm.counts_perm.tracked_insert(0, vmpl0_count_perm);
    }
    let vmpl0_state = cpu_taken.nested_irq.state.load(
        Tracked(&mut cpu_perm.irq_state_perm.state_perm),
    );

    let mut vmpl1_present = false;
    let mut vmpl1_count: i32 = -1;
    let mut vmpl1_state = false;
    if let Some(ext_vmpl1) = cpu_taken.ext_vmpl1.take() {
        vmpl1_present = true;
        let mut ext_vmpl1 = ext_vmpl1;
        let tracked mut ext_vmpl1_perm = cpu_perm.ext_vmpl1_perm.tracked_take();

        proof_with!(Tracked(&mut ext_vmpl1_perm.nested_irq_perm));
        let tracked mut vmpl1_count_perm =
            ext_vmpl1_perm.nested_irq_perm.counts_perm.tracked_remove(0);
        vmpl1_count = ext_vmpl1.nested_irq.counts[0].load(Tracked(&mut vmpl1_count_perm));
        proof {
            ext_vmpl1_perm.nested_irq_perm.counts_perm.tracked_insert(0, vmpl1_count_perm);
        }
        vmpl1_state =
            ext_vmpl1.nested_irq.state.load(Tracked(&mut ext_vmpl1_perm.nested_irq_perm.state_perm));

        cpu_taken.ext_vmpl1.replace(ext_vmpl1);
        proof {
            cpu_perm.ext_vmpl1_perm = Some(ext_vmpl1_perm);
        }
    }
    this_cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

    kinfo!(
        "nested_irq_state",
        "marker", marker => hex,
        "cur_vmpl", if cur_vmpl1 { 1 } else { 0 },
        "if", if if_enabled { 1 } else { 0 },
        "vmpl0_count", vmpl0_count as i64,
        "vmpl0_state", if vmpl0_state { 1 } else { 0 },
        "vmpl1_present", if vmpl1_present { 1 } else { 0 },
        "vmpl1_count", vmpl1_count as i64,
        "vmpl1_state", if vmpl1_state { 1 } else { 0 }
    );
}

#[verifier::external_body]
pub fn dump_ghcb_shared_buffer(shared_buffer: &Array<PAtomicU8, GHCB_BUFFER_SIZE>) {
    unsafe {
        kinfo!("GHCB Shared Buffer Dump:", core::slice::from_raw_parts(
            shared_buffer.index_as_ptr(0).0.addr() as *const u8,
            GHCB_BUFFER_SIZE,
        ) => hex);
    }
}

pub fn dump_frame_allocator_usage() -> u64 {
    DEKO_FRAME_ALLOCATOR_FULL.0.remaining()
}

#[verifier::external_body]
pub fn err_dump_vmsa() {
    let (cpu, Tracked(_cpu_perm)) = DekoCpuCtx::this_cpu();
    let this_vmsa = VMSA::this_vmsa(cpu);
    let vmsa = unsafe { &*(this_vmsa.addr() as *const VMSA) };
    kerror!("VMSA dump:", vmsa);
}

#[verus_spec(
    with
        Tracked(perm): Tracked<&DekoRunQueuePermission>,
    requires
        queue.wf(),
        queue.wf_with(*perm),
)]
pub fn log_runqueue_info(queue: &DekoRunQueue) {
    kinfo!("Runqueue info:");
    if let Some(current) = &queue.current {
        kinfo!("  Current task: ", current.as_ref().data);
    } else {
        kinfo!("  Current task: None");
    }
    if let Some(idle) = &queue.idle {
        kinfo!("  Idle task: ", idle.as_ref().data);
    } else {
        kinfo!("  Idle task: None");
    }
    if let Some(terminated) = &queue.terminated {
        kinfo!("  Terminated task: ", terminated.as_ref().data);
    } else {
        kinfo!("  Terminated task: None");
    }
    if let Some(wake) = &queue.wake {
        kinfo!("  Wake task: ", wake.as_ref().data);
    } else {
        kinfo!("  Wake task: None");
    }

    if let Some(head) = queue.run_list.head.as_ref() {
        let mut ptr = head;
        let len = queue.run_list.len();
        kinfo!("  Runlist length: ", len);

        for i in 0..len
            invariant
                0 <= i <= queue.run_list@.len(),
                queue.run_list.wf(),
                len == queue.run_list@.len() == queue.run_list.inner@.ptrs.len(),
                i < queue.run_list@.len() ==> {
                    &&& ptr == queue.run_list.inner@.ptrs[i as int]
                    &&& queue.run_list.node_wf_at(i as nat)
                },
                queue.run_list.head.is_some(),
        {
            let v = ptr.borrow(
                Tracked(queue.run_list.inner.borrow().perms.tracked_borrow(i as nat)),
            );

            kinfo!("  Runlist[", i, "]: ", v.value.as_ref().data);

            if i + 1 < len {
                ptr = v.next.as_ref().unwrap();
            }
        }
    }
}

} // verus!
