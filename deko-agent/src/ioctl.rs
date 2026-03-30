use std::fs::File;
use std::io;
use std::mem::size_of;
use std::os::fd::AsRawFd;

const DEKO_IOC_MAGIC: u64 = 0xDD;
const IOC_NRBITS: u64 = 8;
const IOC_TYPEBITS: u64 = 8;
const IOC_SIZEBITS: u64 = 14;
const IOC_NRSHIFT: u64 = 0;
const IOC_TYPESHIFT: u64 = IOC_NRSHIFT + IOC_NRBITS;
const IOC_SIZESHIFT: u64 = IOC_TYPESHIFT + IOC_TYPEBITS;
const IOC_DIRSHIFT: u64 = IOC_SIZESHIFT + IOC_SIZEBITS;
const IOC_WRITE: u64 = 1;
const IOC_READ: u64 = 2;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BindingReq {
    pub mnt_ns_id: u64,
    pub domain_id: u32,
    pub reserved: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct LookupReq {
    pub mnt_ns_id: u64,
    pub domain_id: u32,
    pub found: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct LoadPolicyReq {
    pub domain_id: u32,
    pub reserved: u32,
    pub policy_ptr: u64,
    pub policy_len: u64,
}

const fn ioc(direction: u64, ioc_type: u64, nr: u64, size: usize) -> u64 {
    (direction << IOC_DIRSHIFT)
        | (ioc_type << IOC_TYPESHIFT)
        | (nr << IOC_NRSHIFT)
        | ((size as u64) << IOC_SIZESHIFT)
}

const fn iow(ioc_type: u64, nr: u64, size: usize) -> u64 { ioc(IOC_WRITE, ioc_type, nr, size) }

const fn iowr(ioc_type: u64, nr: u64, size: usize) -> u64 {
    ioc(IOC_WRITE | IOC_READ, ioc_type, nr, size)
}

pub const DEKO_IOC_BIND_DOMAIN: u64 = iow(DEKO_IOC_MAGIC, 0x01, size_of::<BindingReq>());
pub const DEKO_IOC_LOOKUP_DOMAIN: u64 = iowr(DEKO_IOC_MAGIC, 0x02, size_of::<LookupReq>());
pub const DEKO_IOC_UNBIND_DOMAIN: u64 = iow(DEKO_IOC_MAGIC, 0x03, size_of::<BindingReq>());
pub const DEKO_IOC_LOAD_POLICY: u64 = iow(DEKO_IOC_MAGIC, 0x04, size_of::<LoadPolicyReq>());

fn ioctl_ptr<T>(file: &File, req: u64, arg: &mut T) -> io::Result<()> {
    let rc = unsafe { libc::ioctl(file.as_raw_fd(), req, arg as *mut T) };
    if rc < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

pub fn bind_domain(file: &File, mnt_ns_id: u64, domain_id: u32) -> io::Result<()> {
    let mut req = BindingReq { mnt_ns_id, domain_id, reserved: 0 };
    ioctl_ptr(file, DEKO_IOC_BIND_DOMAIN, &mut req)
}

pub fn lookup_domain(file: &File, mnt_ns_id: u64) -> io::Result<LookupReq> {
    let mut req = LookupReq { mnt_ns_id, domain_id: 0, found: 0 };
    ioctl_ptr(file, DEKO_IOC_LOOKUP_DOMAIN, &mut req)?;
    Ok(req)
}

pub fn unbind_domain(file: &File, mnt_ns_id: u64, domain_id: u32) -> io::Result<()> {
    let mut req = BindingReq { mnt_ns_id, domain_id, reserved: 0 };
    ioctl_ptr(file, DEKO_IOC_UNBIND_DOMAIN, &mut req)
}

pub fn load_policy(file: &File, domain_id: u32, policy_bytes: &[u8]) -> io::Result<()> {
    let mut req = LoadPolicyReq {
        domain_id,
        reserved: 0,
        policy_ptr: policy_bytes.as_ptr() as u64,
        policy_len: policy_bytes.len() as u64,
    };
    ioctl_ptr(file, DEKO_IOC_LOAD_POLICY, &mut req)
}
