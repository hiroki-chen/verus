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
use vstd::prelude::*;

use crate::cpu::task::{DekoRunnableCtx, X86ExceptionContext};
use crate::kinfo;

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
            kinfo!("check_unwound_frame: rsp", rsp, "rbp", rbp, "not in any stack");
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

    #[verifier::external_body]
    pub fn unwind_this_cpu() -> Self {
        let mut rbp: usize;
        // SAFETY: Inline assembly to read RBP, which does not change any state
        // related to memory safety.
        unsafe {
            core::arch::asm!("
                movq %rbp, {}",
                out(reg) rbp,
                options(att_syntax),
            );
        };

        todo!()
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
    // At this time the allocator must be initialized.
    let mut msg = alloc::format!("  [{:016x}]", frame.rip.0);

    if frame.is_exception_frame {
        msg.push_str(" @");
        annotated = true;
    }
    if !frame.is_aligned {
        msg.push_str(if annotated { "#" } else { " #" });
    }
    kinfo!(msg.as_str());
}

#[verifier::external_body]
pub fn print_stack(skip: usize) {
    return;

    let unwinder = StackUnwinder::unwind_this_cpu();
    kinfo!("---BACKTRACE---:");
    for frame in unwinder.skip(skip) {
        match frame {
            UnwoundStackFrame::Valid(item) => print_stack_frame(item),
            UnwoundStackFrame::Invalid => kinfo!("  Invalid frame"),
        }
    }
    kinfo!("---END---");
}


} // verus!
