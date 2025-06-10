# CAGE: Formally Verified SM-Based Intra-VM Compartmentalization for CVMs

## Credits

We sincerely express gratitude to Microsoft for open-sourcing VeriSMo.

```txt
tools/ : includes verifier and compiler tools and scripts.
deps/ : includes hacl package
source/ : verismo code
source/verismo : verified code for verismo
source/verismo_main : main executable bin, which only defines a unverified Rust panic handler.
source/verismo/src/arch : model
source/verismo/src/entry.s : a small and unverified assembly code.
source/target.json : target configuration
```
