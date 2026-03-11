# Agent Directives

## Environment and Setup
- **Configuration Check:** Inspect `.cargo/config.toml` prior to execution to identify specific build instructions, target architectures, and environment setup aliases.
- **Toolchain:** Ensure the environment is configured for both the Rust compiler and the Verus verification engine.

## Code Style and Verification
- **Dual Compliance:** Adhere strictly to idiomatic Rust patterns and Verus formal verification syntax.
- **Specifications:** Use `#[verus_spec(...)]` for all function contracts. Ensure post-conditions account for both register states and memory safety.
- **Opaque Bodies:** Do not apply `#[verifier::external_body]` carelessly. You must request explicit user authorization before adding this annotation.

## Low-Level System Implementation
- **Resource Control:** Explicitly define and track resource ownership. 
- **CPU State:** When manipulating processor state, ensure `EFLAGS` and general-purpose registers are managed accurately.
- **Interrupt Handling:** Implement Interrupt Descriptor Table (IDT) handlers, Task Priority Registers (TPR), and Interrupt Service Routines (ISRs) with strict verification.
- **State Transitions:** Validate all register states at boundary entry and exit points.

## Interaction Protocol
- **Verification Failures:** If Verus fails to prove a specification, report the specific proof failure and suggest refinements. Do not autonomously bypass verification.
- **Communication:** Prioritize concise, professional communication in all code comments and status updates.
