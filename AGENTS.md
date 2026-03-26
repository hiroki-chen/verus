# AGENTS.md

## Environment and Setup

- Before building or running anything, inspect `.cargo/config.toml` to identify project-specific aliases, target architectures, linker settings, and environment bootstrapping commands.
- Use the aliases defined there for bootstrap, build, check, test, and run workflows whenever available.
- Ensure both the Rust toolchain and the Verus toolchain are installed and correctly configured before making verification-related changes.
- After every code modification, run `cargo pretty`.

## Coding and Verification Standards

- Code must satisfy both idiomatic Rust conventions and Verus verification requirements.
- Keep specifications explicit and local. Prefer small functions with clear contracts over large functions with mixed proof and implementation logic.
- Use `#[verus_spec(...)]` for function contracts.
- Postconditions must account for:
  - register-state correctness,
  - memory safety,
  - ownership and resource invariants,
  - boundary-state preservation where applicable.
- Do not add `#[verifier::external_body]` without explicit user approval.
- Do not introduce `axiom` or `admit` unless absolutely necessary due to proof limitations, such as unavoidable raw-pointer casting boundaries. If such a step is needed, explain the exact blocker first.
- Always choose triggers for quantifiers for proof searching and performance to help SMT solvers instantiate predicates, proof conditions, etc.
- Use `#[verus_spec(invariant ...)]` above the loop block when you apply loop invariant.

## Naming Conventions

- Spec functions must end with `_spec`.
- Proof functions must begin with `lemma_`.
- Proof functions that construct `tracked` objects must begin with `tracked_`.
- The same naming rules apply to axioms if axioms are ever introduced.

## Verus Structural Rules

- Do not place code outside the `verus!` block unless it is limited to:
  - imports,
  - module declarations,
  - other required non-Verus glue code.
- Avoid `for` loops and iterator-based constructs when proof stability is important, since Verus support for these patterns is limited. Prefer `while` loops with explicit invariants.
- Do not use `#[verifier::external_body]` as a debugging shortcut or to test whether proof failures disappear.

## Low-Level System Rules

- Do not use `Vec` or `String` from `alloc` directly, since they assume a `GlobalAllocator`, which is forbidden in this system.
- Use the crate-provided allocator-aware aliases built on `DekoAllocatorApi`.
- Make ownership and resource control explicit at all system boundaries.
- When manipulating CPU state, model and preserve:
  - general-purpose registers,
  - `EFLAGS`,
  - any architecture-specific state touched by the operation.
- For interrupt-related code, verify:
  - IDT handler setup,
  - TPR interactions,
  - ISR entry and exit conditions,
  - boundary-state transitions.
- Validate entry and exit state transitions for all routines that cross privilege, interrupt, or hardware-control boundaries.

## Proof Development Policy

- If Verus cannot prove a specification, do not bypass the failure silently.
- Report the exact proof failure and propose a refinement, such as:
  - stronger preconditions,
  - intermediate lemmas,
  - better decomposition,
  - sharper invariants,
  - reduced solver load.
- Prefer proof decomposition over large monolithic proof functions.
- For proof-heavy functions that may stress the solver, consider `#[verifier::spinoff_prover]`.

## Preferred Proof Techniques

### Function decomposition
- Break large workflows into smaller verified components with precise preconditions and postconditions.
- Separate executable logic, spec logic, and proof logic when doing so improves solver performance or readability.

### Solver load control
- Use `#[verifier::spinoff_prover]` on proof-heavy functions where parallel SMT solving may help.
- Introduce helper lemmas instead of forcing the solver through a large proof obligation in one step.
- Use `#[verifier::inline]` to inline some simple spec functions to avoid extra overhead for definition unfolding.

## Communication and Change Discipline

- Keep status updates and code comments concise and technical.
- When verification fails, explain the failure precisely rather than masking it.
- Do not weaken guarantees, add proof escapes, or suppress obligations without explicit justification.
