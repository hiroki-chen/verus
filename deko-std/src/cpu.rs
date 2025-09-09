use vstd::prelude::*;

use crate::prelude::*;

verus! {

#[verifier::external_body]
pub fn flush_tlb(addr: u64) {
    // Flush TLB for the new mapping
    unsafe {
        core::arch::asm!("invlpg [{}]", in(reg) addr);
    }
}

pub enum PrivilegeLevel {
    /// Ring 0, the most privileged level.
    Root,
    /// Ring 3, typically used for device drivers.
    User,
}

/// We discard other privilege levels as they are now under-utilized and
/// we found that two are sufficient for our purposes.
pub enum VmPrivilegeLevel {
    /// L1 VM on Intel or VMPL 0 on AMD
    Root,
    /// L2 VM on Intel or VMPL 3 on AMD
    NonRoot,
}

pub ghost struct CpuCoreStatus {
    /// The privilege level of the CPU core.
    pub privilege_level: PrivilegeLevel,
    /// The VM privilege level of the CPU core.
    pub vm_privilege_level: VmPrivilegeLevel,
    /// The ID of the CPU core.
    pub cpu: nat,
    /// Whether the CPU core is currently running.
    pub running: bool,
}

pub enum RegisterName {
    Rflags,
    Rax,
    Rsp,
    Cs,
    Ds,
    Ss,
    Es,
    Gs,
    Cpl,
    Cr0,
    Cr1,
    Cr2,
    Cr3,
    Cr4,
    XCr0,
    IdtrBaseLimit,
    GdtrBaseLimit,
    MSR(u32),
}

pub enum RflagsBit {
    CF = 0,  // Carry flag
    R1 = 1,
    PF = 2,
    R2 = 3,
    AF = 4,
    R3 = 5,
    ZF = 6,
    SF = 7,
    TF = 8,  // Trap flag
    IF = 9,  // Interrupt enable flag
    DF = 10,
    ID = 21,  // Able to use CPUID
}

pub type RegisterMap = Map<RegisterName, Register>;

#[verifier(external_body)]
pub tracked struct Register {
    __marker: NoCopy,
}

/// A view of a register value in a CPU core.
pub ghost struct RegisterValueView<T> {
    // Name of the parent core.
    pub cpu: nat,
    /// The name of the register.
    pub name: RegisterName,
    /// Is shared among other cores?
    pub shared: bool,
    /// The value it holds.
    pub value: T,
}

impl<T: WellFormed> RegisterValueView<T> {
    pub open spec fn shared(&self) -> bool {
        self.shared
    }

    pub open spec fn value(&self) -> T {
        self.value
    }

    pub open spec fn wf(&self) -> bool {
        // The view is well-formed if the value is well-formed.
        self.value.wf()
    }
}

/// Abstraction over a cpu core.
pub tracked struct CpuCore {
    /// The CPU VM privilege level.
    pub priv_level: nat,
    /// The ID of the CPU core.
    pub cpu: nat,
    pub regs: RegisterMap,
}

#[verifier(external_body)]
pub tracked struct CpuCoreId {
    __marker: NoCopy,
}

impl Register {
    pub uninterp spec fn wf(&self) -> bool;

    pub open spec fn view<T>(&self) -> RegisterValueView<T> {
        RegisterValueView {
            cpu: self.cpu(),
            name: self.name(),
            shared: self.shared(),
            value: self.value(),
        }
    }

    pub uninterp spec fn name(&self) -> RegisterName;

    pub uninterp spec fn shared(&self) -> bool;

    /// Parent CPU id.
    pub uninterp spec fn cpu(&self) -> nat;

    pub open spec fn wf_notshared(&self) -> bool {
        &&& self.wf()
        &&& !self.shared()
    }

    pub uninterp spec fn value<T: Sized>(
        &self,
    ) -> T;
    // #[verifier(external_body)]
    // pub broadcast proof fn axiom_eq<T>(x: Self, y: Self)
    //     requires
    //         x.view::<T>() === y.view::<T>(),
    //     ensures
    //         (x === y),
    // {
    // }
    // #[verifier(external_body)]
    // pub broadcast proof fn axiom_wf<T: WellFormed>(&self)
    //     ensures
    //         self.wf() == self.view::<T>().wf(),
    // {
    // }

}

impl CpuCoreId {
    pub uninterp spec fn view(&self) -> CpuCoreStatus;
}

} // verus!
