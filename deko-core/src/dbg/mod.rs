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
use deko_std::cpu::X86GeneralRegs;
use deko_std::deko_rwlock_read_atomic_data;
use deko_std::mem::STACK_SIZE;
use deko_std::ptr::DekoPPtr;
use vstd::prelude::*;

use crate::cpu::task::{DekoRunnableCtx, X86ExceptionContext};
use crate::cpu::DekoCpuCtx;
use crate::imp::doorbell::HVDoorbell;
use crate::kinfo;
use crate::logging::{print_str, CONSOLE, CONSOLE_LOCK};
use crate::snp::doorbell::HV_DOORBELL_NO_FURTHER_SIGNAL_FLAG;
use crate::snp::is_vmpl1;

verus! {

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

} // verus!
