// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Jon Lange (jlange@microsoft.com)
//         Hiroki Chen (haobchen@iu.edu)
use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::bits::bit_u64_and_auto;
use deko_std::boxed::Box;
use deko_std::prelude::DekoPointsTo;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use deko_std::{deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data};
use vstd::prelude::*;

use crate::collections::{update_slice, update_vec};
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission, CPUID_MAX_COUNT, PERCPU_AREAS};
use crate::guest::CaaArea;
use crate::imp::ghcb::GuestHostCommunicationBlock;
use crate::imp::vmsa::VMSA;
use crate::imp::{rdtsc, wrmsr, SnpStatusFlags, REST_INJ};
use crate::snp::rdmsr;
use crate::{kdebug, kerror, kinfo, kpanic_if, kwarn};

verus! {

/// A representation of the x86 APIC (x2APIC).
#[derive(DekoDebug)]
pub struct X86Apic;

pub const APIC_LVT_TIMER_TSC_DEADLINE: u64 = 0x2 << 17;

// 10b at 18:17
pub const APIC_LVT_MASKED: u64 = 1 << 16;

pub const APIC_LVT_DELIVERY_MODE_MASK: u64 = 0x7 << 8;

// bits 10:8
pub const APIC_LVT_TIMER_MODE_MASK: u64 = 0x3 << 17;

// bits 18:17
pub const APIC_LVT_VECTOR_MASK: u64 = 0xFF;

// bits 7:0
pub const SVSM_TIMER_VECTOR: u64 = 0xEF;

pub const IA32_X2APIC_LVT_TIMER: u32 = 0x00000832;

pub const IA32_TSC_DEADLINE: u32 = 0x000006E0;

pub const IA32_X2APIC_EOI: u32 = 0x0000080B;

pub const MSR_X2APIC_BASE: u32 = 0x800;

/// APIC Base MSR
pub const MSR_APIC_BASE: u32 = 0x1B;

/// Local APIC ID register MSR offset
pub const APIC_OFFSET_ID: usize = 0x2;

/// End-of-Interrupt register MSR offset
pub const APIC_OFFSET_EOI: usize = 0xB;

/// Spurious-Interrupt-Register MSR offset
pub const APIC_OFFSET_SPIV: usize = 0xF;

/// Interrupt-Service-Register base MSR offset
pub const APIC_OFFSET_ISR: usize = 0x10;

/// Interrupt-Control-Register register MSR offset
pub const APIC_OFFSET_ICR: usize = 0x30;

/// SELF-IPI register MSR offset (x2APIC only)
pub const APIC_OFFSET_SELF_IPI: usize = 0x3F;

/// Software Enable bit mask for Spurious Interrupt Vector Register
pub const APIC_SPIV_SW_ENABLE_MASK: u64 = 1 << 8;

/// Represents the Local APIC of a CPU.
pub trait Apic: deko_std::fmt::DekoDebug + WellFormed {
    /// Reads the APIC ID.
    #[inline]
    fn id(&self) -> (r: u32)
        requires
            self.wf(),
        ensures
            self.wf(),
            r < CPUID_MAX_COUNT,
    {
        let r = self.apic_read(APIC_OFFSET_ID as u32);
        kpanic_if!(r >= CPUID_MAX_COUNT as u32, "APIC ID {} exceeds maximum CPU count {}", r, CPUID_MAX_COUNT);
        r
    }

    /// Updates the APIC_BASE MSR with the given masks.
    fn apic_base(&self, and_mask: u64, or_mask: u64)
        ensures
            self.wf(),
    ;

    /// Writes `value` to the APIC register at `reg`.
    fn apic_write(&self, reg: u32, value: u64)
        requires
            self.wf(),
            reg <= 0xFF,
    ;

    fn spiv_write(&self, vector: u8, enable: bool)
        requires
            self.wf(),
    ;

    /// Reads the APIC register at `reg`.
    fn apic_read(&self, reg: u32) -> u32
        requires
            self.wf(),
            reg <= 0xFF,
    ;

    fn icr_write(&self, low: u32, high: u32)
        requires
            self.wf(),
    {
        broadcast use SnpStatusFlags::lemma_each_bit_is_valid;

        if SnpStatusFlags::get_status().contains(REST_INJ) {
            // Forward this to HV doorbell.
            let (ghcb, Tracked(perm)) = crate::snp::ghcb::current_ghcb();
            GuestHostCommunicationBlock::hv_ipi(
                ghcb,
                Tracked(perm),
                (low as u64 | ((high as u64) << 32)),
            );
        } else {
            self.apic_write(APIC_OFFSET_ICR as u32, (low as u64 | ((high as u64) << 32)));
        }
    }

    /// End of Interrupt signal to the APIC.
    fn eoi(&self)
        requires
            self.wf(),
    {
        self.apic_write(APIC_OFFSET_EOI as u32, 0);
    }
}

impl Apic for X86Apic {
    fn apic_base(&self, and_mask: u64, or_mask: u64)
        ensures
            self.wf(),
    {
        let current_value = rdmsr(MSR_APIC_BASE);

        kdebug!("Current APIC base MSR value:", current_value => hex);
        let new_value = (current_value & and_mask) | or_mask;
        kdebug!("Updating APIC base MSR to:", new_value => hex);

        if current_value != new_value {
            wrmsr(MSR_APIC_BASE, new_value);
        } else {
            kwarn!("APIC base MSR already has the desired value: {:#x}", new_value);
        }
    }

    fn apic_write(&self, reg: u32, value: u64) {
        let msr = MSR_X2APIC_BASE + reg;

        wrmsr(msr, value);
    }

    fn apic_read(&self, reg: u32) -> u32 {
        let msr = MSR_X2APIC_BASE + reg;

        rdmsr(msr) as u32
    }

    fn spiv_write(&self, vector: u8, enable: bool) {
        let apic_spiv = if enable {
            APIC_SPIV_SW_ENABLE_MASK
        } else {
            0
        } | ((vector as u64) & 0xFF);

        self.apic_write(APIC_OFFSET_SPIV as u32, apic_spiv);
    }
}

impl WellFormed for X86Apic {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl X86Apic {
    /// Enables the x2APIC mode in the APIC.
    #[inline]
    pub fn enable(&self) {
        let enable = 0x800 | 0x400;
        self.apic_base(!enable, enable);
    }

    #[inline]
    pub fn sw_enable(&self) {
        self.spiv_write(0xFF, true);
    }
}

/// A representation of the x86 Local APIC on this core.
#[derive(DekoDebug)]
pub struct X86LocalApic {
    /// The Interrupt Command Register (ICR) low and high parts.
    pub icr_low: u32,
    pub icr_high: u32,
    /// Whether the APIC needs to be updated for the guest state.
    pub need_update: bool,
    /// Whether an interrupt has been delivered.
    pub interrupt_delivered: bool,
    /// Whether an NMI is pending delivery.
    pub nmi_pending: bool,
    /// Whether an interrupt is queued for delivery.
    pub interrupt_queued: bool,
    /// Whether a lazy EOI is pending.
    pub lazy_eoi_pending: bool,
    /// The Interrupt Request Register (IRR) bits.
    pub irr: [u32; 8],
    pub isr: usize,
    /// The In-Service Register (ISR) bits.
    pub isr_stack: [u8; 16],
    /// Trigger mode registers.
    pub tmr: [u32; 8],
}

impl WellFormed for X86LocalApic {
    open spec fn wf(&self) -> bool {
        &&& self.irr@.len() == 8
        &&& self.isr_stack@.len() == 16
        &&& self.tmr@.len() == 8
        &&& self.isr <= 16
    }
}

#[verus_verify]
impl X86LocalApic {
    pub open spec fn is_pending(&self, vector: u8) -> bool {
        let index = (vector / 32) as int;
        let offset = (vector % 32) as int;
        if index >= 0 && index < 8 {
            (self.irr[index] & (1u32 << offset)) != 0
        } else {
            false
        }
    }

    #[verus_spec(r =>
        ensures
            r.wf(),
            r.irr@ == Seq::new(8, |i: int| 0u32),
            r.isr@ == 0,
            r.isr_stack@ == Seq::new(16, |i: int| 0u8),
            r.tmr@ == Seq::new(8, |i: int| 0u32),
            r.icr_low@ == 0,
            r.icr_high@ == 0,
            r.need_update@ == false,
            r.interrupt_queued@ == false,
            r.lazy_eoi_pending@ == false,
            r.interrupt_delivered@ == false,
            r.nmi_pending@ == false,
    )]
    pub fn new() -> Self {
        X86LocalApic {
            icr_low: 0,
            icr_high: 0,
            need_update: false,
            interrupt_delivered: false,
            nmi_pending: false,
            interrupt_queued: false,
            lazy_eoi_pending: false,
            irr: [0;8],
            isr: 0,
            isr_stack: [0;16],
            tmr: [0;8],
        }
    }

    /// Acknowledges the EOI from the guest by clearing the call_pending bit
    /// in the CAA area.
    #[verus_spec(r =>
        with
            Tracked(caa_perm): Tracked<&mut DekoPointsTo<CaaArea>>,
        requires
            old(caa_perm).wf(),
            old(caa_perm).is_init(),
            old(caa_perm).pptr() == caa@,
        ensures
            caa_perm.wf(),
            caa_perm.is_init(),
            caa_perm.pptr() == caa@,
            caa_perm.value().no_eoi_required == 0,
    )]
    pub fn clear_guest_eoi(caa: DekoPPtr<CaaArea>) {
        let mut caa_area = caa.take(Tracked(caa_perm));
        caa_area.no_eoi_required = 0;

        caa.write(Tracked(caa_perm), caa_area);
    }

    /// Consumes host interrupts.
    #[verus_spec(
        requires
            old(self).wf(),
        ensures
            self.wf(),
    )]
    pub fn consume_host_interrupts(&mut self) {
        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();

        let hv_doorbell = &cpu.borrow(Tracked(&cpu_perm.ptr_perm)).doorbell;
        kpanic_if!(
            core::hint::unlikely(hv_doorbell.is_none()),
            "HV doorbell not initialized when consuming host interrupts",
        );

        let vmpl_event_mask =
            deko_rwlock_write_atomic_data! {
            hv_doorbell.as_ref().unwrap(),
            hv_doorbell_ptr,
            hv_doorbell_perm,
            {
                let mut hv_doorbell = hv_doorbell_ptr.take(Tracked(&mut hv_doorbell_perm.borrow_mut().ptr_perm));

                let v = hv_doorbell.per_vmpl_events.swap(
                    Tracked(&mut hv_doorbell_perm.borrow_mut().hv_perm.per_vmpl_events_perm),
                    0,
                );

                // Put back the doorbell.
                hv_doorbell_ptr.write(Tracked(&mut hv_doorbell_perm.borrow_mut().ptr_perm), hv_doorbell);

                v
            }
        };

        if vmpl_event_mask & (1 << (2 - 1)) == 0 {
            return ;
        }
        kinfo!("Consuming host interrupts for guest APIC");
    }

    /// If any IPI is pending when we process it.
    #[verus_spec(
        with
            Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
        requires
            old(self).wf(),
            old(cpu_perm).wf_with(cpu),
        ensures
            self.wf(),
            cpu_perm.wf_with(cpu),
    )]
    pub fn process_ipi(&mut self, cpu: DekoPPtr<DekoCpuCtx>) {
    }

    #[verus_spec(
        with
            Tracked(caa_perm): Tracked<&mut DekoPointsTo<CaaArea>>,
            Tracked(vmsa_perm): Tracked<&mut DekoPointsTo<VMSA>>,
        requires
            old(self).wf(),
            old(caa_perm).wf(),
            old(caa_perm).is_init(),
            old(caa_perm).pptr() == caa@,
            old(vmsa_perm).wf(),
            old(vmsa_perm).is_init(),
            old(vmsa_perm).pptr() == vmsa@,
        ensures
            self.wf(),
            caa_perm.wf(),
            caa_perm.is_init(),
            caa_perm.pptr() == caa@,
            vmsa_perm.wf(),
            vmsa_perm.is_init(),
            vmsa_perm.pptr() == vmsa@,
    )]
    pub fn check_delivered_interrupts(&mut self, vmsa: DekoPPtr<VMSA>, caa: DekoPPtr<CaaArea>) {
        // Check if any interrupt has been delivered.
        if self.interrupt_delivered {
            proof_with!(Tracked(vmsa_perm));
            let irq = VMSA::check_and_clear_pending_interrupt_event(vmsa);

            if irq != 0 {
                // rewind the pending interrupt.
                self.rewind_pending_interrupt(irq);
                self.lazy_eoi_pending = false;
            }
            self.interrupt_delivered = false;
        }
        // Check to see if a previously queued interrupt is still pending.
        // If so, move it back to the IRR.

        if self.interrupt_queued {
            proof_with!(Tracked(vmsa_perm));
            let irq = VMSA::check_and_clear_pending_virtual_interrupt(vmsa);
            if irq != 0 {
                self.rewind_pending_interrupt(irq);
                self.lazy_eoi_pending = false;
            }
            self.interrupt_queued = false;
        }
        // If a lazy EOI is pending, then check to see whether an EOI has been
        // requested by the guest. Note that if a lazy EOI was dismissed
        // above, the guest lazy EOI flag need not be cleared here, since
        // dismissal of any interrupt above will require reprocessing of
        // interrupt state prior to guest reentry, and that reprocessing will
        // reset the guest lazy EOI flag.

        if self.lazy_eoi_pending {
            let caa = caa.borrow(Tracked(caa_perm));
            if caa.no_eoi_required == 0 {
                kpanic_if!(
                    core::hint::unlikely(self.isr == 0),
                    "ISR stack underflow when processing lazy EOI",
                );

                self.perform_eoi();
            }
        }
    }

    #[verus_spec(
        requires
            old(self).wf(),
            old(self).isr > 0,
        ensures
            self.wf(),
    )]
    fn perform_eoi(&mut self) {
        self.isr = self.isr - 1;  // no underflow because of precondition

        let v = self.isr_stack[self.isr];
        kpanic_if!(
            core::hint::unlikely((v >> 5) >= 8),
            "ISR stack corrupted when performing EOI",
        );

        proof {
            assert(v & 31 < 32) by (bit_vector);
        }

        // Check the vector on the tmr.
        if self.tmr[(v as usize) >> 5] & (1u32 << (v & 31)) != 0 {
        }
        self.need_update = true;
        self.lazy_eoi_pending = false;
    }

    #[verus_spec(
        requires
            old(self).wf(),
            irq != 0,
        ensures
            self.wf(),
    )]
    fn rewind_pending_interrupt(&mut self, irq: u8) {
        let Some(new_index) = self.isr.checked_sub(1) else {
            kerror!("ISR stack underflow when rewinding pending interrupt");
            return ;
        };

        // update the isr stack properly
        kpanic_if!(
            core::hint::unlikely((irq >> 5) >= 8),
            "Invalid IRQ when rewinding pending interrupt: ",
            irq
        );

        let irq_mask = (irq & 31) as u32;
        let old_v = self.irr[(irq >> 5) as usize];

        proof {
            assert(irq_mask < 32) by (bit_vector)
                requires
                    irq_mask == (irq as u8) & 31,
            ;
        }

        let new_v = old_v | (1u32 << irq_mask);
        update_slice(&mut self.irr, (irq >> 5) as _, new_v);

        // Pop the ISR stack.
        self.isr = new_index;
        self.need_update = true;
    }

    /// Serves a guest request to the SVSM.
    #[verus_spec(
        with
            Tracked(caa_perm): Tracked<&mut DekoPointsTo<CaaArea>>,
            Tracked(vmsa_perm): Tracked<&mut DekoPointsTo<VMSA>>,
        requires
            old(self).wf(),
            old(caa_perm).wf(),
            old(caa_perm).is_init(),
            old(caa_perm).pptr() == caa@,
            old(vmsa_perm).wf(),
            old(vmsa_perm).is_init(),
            old(vmsa_perm).pptr() == vmsa@,
        ensures
            self.wf(),
            caa_perm.wf(),
            vmsa_perm.wf(),
    )]
    pub fn serve_guest(&mut self, cpu_index: usize, caa: DekoPPtr<CaaArea>, vmsa: DekoPPtr<VMSA>) {
        self.consume_host_interrupts();

        // Check if an IPI is pending.
        let ipi_pending =
            deko_rwlock_write_atomic_data! {
            PERCPU_AREAS,
            percpu_area,
            percpu_area_perm,
            {
                crate::check_shared_cpu_idx!(cpu_index, percpu_area, percpu_area);

                let tracked mut shared_perm_this = percpu_area_perm.borrow_mut().shared_perms.tracked_remove(cpu_index as int);

                let r = percpu_area.0[cpu_index].ipi_pending.swap(
                    Tracked(&mut shared_perm_this.ipi_pending_perm),
                    false,
                );

                // Put back the shared perm.
                proof {
                    percpu_area_perm.borrow_mut().shared_perms.tracked_insert(cpu_index as int, shared_perm_this);
                }

                r
            }
        };

        if ipi_pending {
            // Process the IPI.
            let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
            let cpu_id = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).cpu_id;

            // A sanity check just to ensure that we are processing the IPI on the correct CPU.
            kpanic_if!(
                core::hint::unlikely(cpu_index != cpu_id as usize),
                "CPU index mismatch when processing guest interruopts",
                cpu_index,
                cpu_id as usize
            );

            proof_with!(Tracked(&mut cpu_perm));
            self.process_ipi(cpu);
        }
        // Check if we need to update.

        if self.need_update {
            // Make sure that all previously delivered interrupts have been
            // processed before attempting to process any more.
            proof_with!(Tracked(caa_perm), Tracked(vmsa_perm));
            self.check_delivered_interrupts(vmsa, caa);
            self.need_update = false;

            if self.nmi_pending {
                // todo.
                // First we do the MNI delivery.
                self.nmi_pending = false;
            }
            let irq = self.scan_irr().unwrap_or(0);
            let current_priority = if self.isr != 0 {
                self.isr_stack[self.isr - 1]
            } else {
                0
            };

            self.lazy_eoi_pending = false;

            let mut guest_caa = caa.take(Tracked(caa_perm));
            guest_caa.no_eoi_required = 0;
            caa.write(Tracked(caa_perm), guest_caa);

            // Determine whether this interrupt can be injected
            // immediately. If not, queue it for delivery when possible.
            let try_lazy_eoi = if #[verus_spec(with Tracked(vmsa_perm))]
            self.deliver_interrupt_immediately(irq, vmsa) {
                self.interrupt_delivered = true;
                true
            } else {
                self.isr == 0
            };

            // This interrupt is a candidate for delivery only if its priority
            // exceeds the priority of the highest priority interrupt currently
            // in service. This check does not consider TPR, because an
            // interrupt lower in priority than TPR must be queued for delivery
            // as soon as TPR is lowered.
            if (irq & 0xF0) <= (current_priority & 0xF0) {
                return ;
            }
        }
    }

    #[verus_spec(r =>
        with
            Tracked(vmsa_perm): Tracked<&mut DekoPointsTo<VMSA>>,
        requires
            old(self).wf(),
            old(vmsa_perm).wf(),
            old(vmsa_perm).is_init(),
            old(vmsa_perm).pptr() == vmsa@,
        ensures
            self.wf(),
            vmsa_perm.wf(),
            vmsa_perm.wf(),
    )]
    fn deliver_interrupt_immediately(&mut self, irq: u8, vmsa: DekoPPtr<VMSA>) -> bool {
        {
            let vmsa = vmsa.borrow(Tracked(vmsa_perm));
            // the guest has interrupts disabled.
            if vmsa.rflags & 0x200 == 0 {
                return false;
            }
            if vmsa.vintr_ctrl.0 & (1 << 10) != 0 {
                return false;
            }
        }

        // Need to compare the priority...
        // This interrupt can only be delivered if it is a higher priority
        // than the processor's current priority.
        // Let the VMSA deliver the interrupt immediately.
        proof_with!(Tracked(vmsa_perm));
        VMSA::deliver_interrupt_immediately(vmsa, irq)
    }

    /// Scans the IRR and returns the highest priority pending interrupt vector.
    #[verifier::spinoff_prover]
    #[verus_spec(r =>
        requires
            self.wf(),
        ensures
            match r {
                Some(v) => {
                    &&& self.is_pending(v)
                    &&& forall |u: u8| u > v ==> !self.is_pending(u)
                },
                None => forall |v: u8| !self.is_pending(v),
           },
    )]
    fn scan_irr(&self) -> Option<u8> {
        // Gives us the proof that if n != 0 then leading_zeros(n) < 32.
        broadcast use vstd::std_specs::bits::axiom_u32_leading_zeros;

        let mut i = 8usize;
        let mut r = None;
        #[verus_spec(
            invariant_except_break
                self.wf(),
                0 <= i <= 8,
                r is None,
                forall |k: int| i <= k < 8 ==> self.irr[k] == 0,
                forall |u: u8| u >= (i as int) * 32 ==> !self.is_pending(u),
            ensures
                match r {
                    Some(v) => self.is_pending(v) && (forall |u: u8| u > v ==> !self.is_pending(u)),
                    None => forall |v: u8| !self.is_pending(v),
                },
            decreases
                i,
        )]
        while i > 0 {
            let chunk_idx = i - 1;
            let val = self.irr[chunk_idx];

            if val != 0 {
                let lz = val.leading_zeros() as u8;
                let bit_index = 31 - lz;

                let vector = (chunk_idx as u8) * 32 + bit_index;
                r = Some(vector as u8);

                proof {
                    // 0 <= u32_leading_zeros(i) < 32
                    //          ==> (i >> sub(31u32, u32_leading_zeros(i) as u32)) & 1u32 != 0u32,
                    assert(val & (1u32 << bit_index) != 0) by (bit_vector)
                        requires
                            val != 0,
                            bit_index == 31 - lz,
                            lz < 32,
                            (val >> (31 - lz) as u32) & 1u32 != 0u32,
                    ;

                    assert(self.is_pending(vector as u8)) by {
                        assert(vector as int / 32 == chunk_idx as int);
                        assert(vector as int % 32 == bit_index as int);

                    }

                    assert forall|u: u8| u > (vector as u8) implies !self.is_pending(u) by {
                        let u_chunk = (u / 32);
                        let u_bit = (u % 32);

                        if u_chunk > chunk_idx as int {
                        } else {
                            admit();
                        }

                    }
                }

                break ;
            }
            i = i - 1;

            proof {
                assert(forall|u: u8| u >= (i as int) * 32 ==> !self.is_pending(u)) by {
                    admit();
                }
            }
        }

        r
    }
}

with_atomic_pred! {
    X86LocalApic,
    (),
    fields: {},
    perm_fields: {},
    data.wf()
}

} // verus!
