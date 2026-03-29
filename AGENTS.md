# AGENTS.md

## System Layout

This project is a secure monitor running at VMPL0 for SEV-SNP where the guest kernel is untrusted.

- VMPL0 is the root of enforcement inside the guest and is trusted to maintain isolation, memory ownership, interrupt safety, and register-state integrity across boundary transitions.
- VMPL1 runs the monitored secure application and is trusted only within the scope of its own measured code and assigned resources.
- VMPL2 runs the general-purpose Linux kernel and must be treated as untrusted for confidentiality, integrity, and control-flow decisions.
- Any input originating from VMPL2, including memory contents, pointers, requests, interrupt-related state, and protocol fields, must be validated before use.
- No invariant of the monitor or VMPL1 may depend on VMPL2 behaving correctly.

## Environment and Setup

- You MUST inspect `.cargo/config.toml` before running any bootstrap, build, check, test, or run command.
- You MUST prefer the aliases defined in `.cargo/config.toml` over raw Cargo subcommands whenever an alias exists.
- For this repository, `build-deko-snp-debug` is the default build workflow for normal development unless the task explicitly requires a different alias or profile.
- Do NOT use plain `cargo build` if `build-deko-snp-debug` or another project-specific build alias is available for the requested task.
- If multiple build aliases exist, choose the one that most specifically matches the requested target, with preference for Deko SNP debug workflows during routine development.
- Before making verification-related changes, ensure both the Rust toolchain and the Verus toolchain are installed and correctly configured.
- After every code modification, run `cargo pretty`.
- The Linux guest kernel we are using can be found inside `~/.config/qemu.snp.toml`.

## Required Command Selection Policy

- For build tasks, first check `.cargo/config.toml`, then use the most specific matching alias.
- Unless the user explicitly asks for a release build, a non-SNP target, or a different workflow, use `cargo build-deko-snp-debug`.
- Do not substitute generic commands for project aliases. For example, do not replace `cargo build-deko-snp-debug` with `cargo build`.
- If an alias wraps required environment setup, target selection, linker configuration, or bootstrapping, you must use that alias rather than reconstructing the command manually.
- When reporting what you ran, name the exact alias used.

## Default Development Workflow

- Inspect `.cargo/config.toml`.
- Use the repository alias for the task instead of raw Cargo commands.
- For ordinary compile checks in this repository, default to `cargo build-deko-snp-debug`.
- After edits, run `cargo pretty`.
- Then run the smallest relevant verification, check, or test command for the changed component, again preferring repository aliases.

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
