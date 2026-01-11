use vstd::prelude::*;

use crate::policy::{DekoMsrIntercept, DekoMsrInterceptVec0};

verus! {

/// The default MSR intercepts to enable for SEV-SNP guests for lower privileged guests.
pub exec const DEFAULT_MSR_INTERCEPTS: [DekoMsrIntercept; 4] = [
    DekoMsrIntercept::InterceptMsrVec0(DekoMsrInterceptVec0::StarRead),
    DekoMsrIntercept::InterceptMsrVec0(DekoMsrInterceptVec0::StarWrite),
    DekoMsrIntercept::InterceptMsrVec0(DekoMsrInterceptVec0::LstarRead),
    DekoMsrIntercept::InterceptMsrVec0(DekoMsrInterceptVec0::LstarWrite),
];

} // verus!
