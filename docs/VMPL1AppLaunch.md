# VMPL1 App Launch Flow

This note summarizes how a protected user application is launched into VMPL1, based on:

- [`deko-linux/arch/x86/coco/sev/deko.c`](/home/haobchen/deko-linux/arch/x86/coco/sev/deko.c)
- [`deko-core/src/guest/service_extend.rs`](/home/haobchen/cage-sev/deko-core/src/guest/service_extend.rs)
- [`deko-core/src/policy/userapp.rs`](/home/haobchen/cage-sev/deko-core/src/policy/userapp.rs)

## High-Level Flow

1. Linux detects a new container app and reports it to the monitor.
2. The monitor creates a shadow `DekoUserApp` keyed by `tgid`.
3. Linux enters `deko_proxy_loop()` and repeatedly issues `SVSM_EXTEND_LAUNCH_APP`.
4. The monitor either initializes a fresh VMPL1 VMSA or resumes an existing one.
5. When VMPL1 exits for syscall/timer service, Linux handles the event and relaunches the app.

## 1. App Registration

Linux first reports a new app to VMPL0. On the monitor side,
[`handle_deko_service_report_app()`](/home/haobchen/cage-sev/deko-core/src/guest/service_extend.rs#L315)
parses `DekoNewAppReq` and calls
[`register_user_app()`](/home/haobchen/cage-sev/deko-core/src/policy/userapp.rs#L1291).

For Docker apps, the monitor builds a shadow
`DekoUserApp` and inserts it into `DEKO_SHADOW_APP_LIST` under `req.tgid`.
At this point the app is known to the monitor, but it is still in `Created` state.

## 2. Linux Proxy Loop

The actual runtime handoff happens in
[`deko_proxy_loop()`](/home/haobchen/deko-linux/arch/x86/coco/sev/deko.c#L453).

Linux does three important things before entering VMPL1:

- Pins the process memory with `deko_pin_pages()`
- Allocates a per-task shared buffer (`struct deko_shared_buf`)
- Prepares an `SVSM_EXTEND_LAUNCH_APP` call:
  - `rcx = shared buffer`
  - `rdx = tgid`
  - `r9 = pt_regs copy`
  - `r8 = migration_version`

Then it loops:

- call `SVSM_EXTEND_LAUNCH_APP`
- if VMPL1 exits with `DEKO_SERVICE_APP_ENTER_OK`, handle syscall results
- if VMPL1 exits with `DEKO_TIMER_SERVICE`, allow `cond_resched()`
- then issue `SVSM_EXTEND_LAUNCH_APP` again

So Linux does not "launch once"; it acts as the proxy loop around a long-lived VMPL1 app.

## 3. Monitor Launch / Resume

On the monitor side,
[`handle_deko_service_launch_app()`](/home/haobchen/cage-sev/deko-core/src/guest/service_extend.rs#L275)
reads the guest `pt_regs`, checks migration version, and calls
[`try_kick_app()`](/home/haobchen/cage-sev/deko-core/src/policy/userapp.rs#L1396).

`try_kick_app()` decides whether this is:

- an initial launch: `DekoUserAppState::Created`
- a normal resume: `DekoUserAppState::Running`
- a migrated resume: `Running` plus migration handoff state

For the initial launch path:

- [`bind_for_local_run()`](/home/haobchen/cage-sev/deko-core/src/policy/userapp.rs#L943)
  marks the app `Running`
  and binds it to the current CPU
- the shared buffer VA is stored into the app state
- `ctx_vmpl1.vmsa.init_for_app(regs)` builds the first VMPL1 runtime context
- thread bases (`fs_base`, `gs_base`, `kernel_gs_base`) are installed

For the normal running path:

- `prepare_app_resume()` resumes the current VMPL1 context

For migration:

- the monitor restores the saved VMSA snapshot and finalizes the CPU handoff

## 4. Service Model

Once running in VMPL1, the app does not directly talk to Linux.
Instead, it exits through the IFC/service path and Linux handles the request in the proxy loop.

The common cases today are:

- syscall service
- timer service
- migration relaunch

This is why the shared buffer and copied `pt_regs` matter: they form the control channel between
Linux and the VMPL1 runtime.

## Summary

The VMPL1 launch model in this repo is:

- register app once
- keep a shadow `DekoUserApp` in VMPL0
- drive execution from Linux through `deko_proxy_loop()`
- let VMPL0 decide whether each `LAUNCH_APP` is a fresh init, resume, or migrated resume

In short, Linux provides the outer scheduling/proxy loop, while VMPL0 owns the protected VMPL1
runtime state.
