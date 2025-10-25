# Deko Ergonomic Logging System

This document describes how to use the ergonomic logging system designed for Verus-verified code in the Deko project.

## Overview

The Deko logging system provides ergonomic debugging capabilities while working within Verus constraints:

- **No heap allocations** - Uses stack-based string formatting
- **External body wrappers** - Wraps `core::fmt::Arguments` for Verus compatibility
- **Custom DekoDebug trait** - Alternative to `std::fmt::Debug` for no_std environments
- **Rich macro system** - Ergonomic macros for common debugging tasks
- **Platform abstraction** - Works with SNP/TDX platforms via GHCB

## Basic Usage

### Simple Printing

```rust
use deko_core::logging::*;

// Basic string printing
print_str("Hello, world!");
print_str_ln("Hello with newline!");
print_char('A');

// Using macros
log_print!("Hello, {}!", "world");
log_println!("Hello with newline: {}", 42);
```

### Numeric Printing

```rust
// Integers in various formats
let num = 255u32;
print_integer(num);           // 255
print_integer_hex(num);       // ff
print_integer_hex_prefixed(num); // 0xff
print_integer_binary(num);    // 11111111
print_integer_octal(num);     // 377

// Using macros
log_int!(42);
log_hex!(0xDEADBEEF);
log_hex_prefixed!(0x1234);
log_bin!(0b1010);

// Custom base printing
print_uint_base(255u32, 16);  // ff
print_uint_base(255u32, 2);   // 11111111
```

### Float Printing

```rust
let pi = 3.14159;
print_float_decimal(pi);      // 3.14159
print_float_scientific(pi);   // 3.14159e0

// Using macros
log_float!(2.718);
```

## DekoDebug Trait

The `DekoDebug` trait provides heap-free debugging for custom types.

### Basic Types

All primitive types implement `DekoDebug`:

```rust
let x = 42u32;
x.deko_debug();              // Prints: 42

let flag = true;
flag.deko_debug();           // Prints: true

let text = "hello";
text.deko_debug();           // Prints: "hello"
```

### Using DekoDebug Macros

```rust
let value = 42;
let name = "test";

// Debug print with variable name
deko_dbg!(value);            // Prints: [DBG] value = 42

// Debug multiple values
deko_dbg!(value, name);      // Prints: [DBG] value = 42, name = "test", 

// Custom label
deko_print!("My Value", &value);  // Prints: My Value: 42
```

### Custom Implementation

```rust
struct MyStruct {
    id: u32,
    name: &'static str,
    active: bool,
}

impl DekoDebug for MyStruct {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("MyStruct {\n");
        print_str("  id: ");
        print_integer(self.id);
        print_str(",\n  name: \"");
        print_str(self.name);
        print_str("\",\n  active: ");
        print_bool(self.active);
        print_str(",\n}");
    }
}

// Usage
let my_struct = MyStruct { 
    id: 123, 
    name: "example", 
    active: true 
};
my_struct.deko_debug();
```

## Colored Logging Levels

The system provides colored logging with different levels:

```rust
// Error logging (red)
log_error!("Critical error: {}", error_code);

// Warning logging (yellow)
log_warn!("Warning: {} might be invalid", input);

// Info logging (green)
log_info!("System initialized successfully");

// Debug logging (blue)
log_debug!("Debug info: state = {}", state);

// Trace logging (cyan)
log_trace!("Entering function: {}", function_name);
```

## Memory Debugging

### Hex Dumps

```rust
let data = [0x41, 0x42, 0x43, 0x44, 0x45];

// Default 16 bytes per line
log_hex_dump!(&data);

// Custom bytes per line
log_hex_dump!(&data, 8);

// Manual hex dump
print_hex_dump(&data, 16);
```

Output:
```
0000: 41 42 43 44 45          | ABCDE
```

### Memory Addresses

```rust
let ptr: *const u8 = &data[0];
log_addr!(ptr);              // Prints: 0x7fff5fbff000
print_address(ptr);          // Same as above
```

## Conditional Logging

```rust
let debug_enabled = true;

// Conditional logging
log_if!(debug_enabled, "Debug mode is enabled");

// Conditional with complex expression
log_if!(x > 10, "Value {} is greater than 10", x);
```

## Advanced Features

### Option and Result Debugging

The `DekoDebug` trait automatically handles `Option` and `Result` types:

```rust
let maybe_value: Option<u32> = Some(42);
maybe_value.deko_debug();    // Prints: Some(42)

let none_value: Option<u32> = None;
none_value.deko_debug();     // Prints: None

let ok_result: Result<u32, &str> = Ok(42);
ok_result.deko_debug();      // Prints: Ok(42)

let err_result: Result<u32, &str> = Err("failed");
err_result.deko_debug();     // Prints: Err("failed")
```

### Custom Base Printing

```rust
let num = 255u32;

// Binary (base 2)
print_uint_base(num, 2);     // 11111111

// Octal (base 8)
print_uint_base(num, 8);     // 377

// Hexadecimal (base 16)
print_uint_base(num, 16);    // ff

// Base 36 (maximum)
print_uint_base(num, 36);    // 73
```

## Integration with Verus

### External Body Functions

All logging functions are marked with `#[verifier::external_body]` to work with Verus:

```rust
verus! {

fn verified_function(x: u32) -> u32
    requires x > 0,
    ensures result >= x,
{
    // Logging works inside verus! blocks
    log_debug!("Processing value: {}", x);
    
    let result = x + 1;
    
    // Debug the result using DekoDebug
    deko_dbg!(result);
    
    result
}

} // verus!
```

### Feature Gating

All logging is gated behind the `logging` feature. When disabled, all macros expand to nothing:

```toml
# Cargo.toml
[features]
default = []
logging = []
```

```rust
// With logging feature enabled
log_debug!("This will print");

// With logging feature disabled
log_debug!("This becomes a no-op");
```

## Example: Complete Debugging Session

```rust
use deko_core::logging::*;

struct NetworkPacket {
    id: u32,
    size: usize,
    data: &'static [u8],
    valid: bool,
}

impl DekoDebug for NetworkPacket {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("NetworkPacket {\n");
        print_str("  id: ");
        print_integer(self.id);
        print_str(",\n  size: ");
        print_integer(self.size);
        print_str(" bytes,\n  valid: ");
        print_bool(self.valid);
        print_str(",\n  data: ");
        if self.data.len() > 0 {
            print_str("[\n");
            print_hex_dump(self.data, 16);
            print_str("  ]");
        } else {
            print_str("[]");
        }
        print_str("\n}");
    }
}

fn process_packet(packet: &NetworkPacket) {
    log_info!("Processing network packet");
    
    deko_dbg!(packet);
    
    if packet.size == 0 {
        log_warn!("Empty packet received, ID: {}", packet.id);
        return;
    }
    
    log_debug!("Packet validation: {}", packet.valid);
    
    if !packet.valid {
        log_error!("Invalid packet detected!");
        log_hex_dump!(packet.data);
        return;
    }
    
    log_info!("Packet processed successfully");
}

// Usage
let data = b"Hello, World!";
let packet = NetworkPacket {
    id: 0x1234,
    size: data.len(),
    data,
    valid: true,
};

process_packet(&packet);
```

## Performance Considerations

1. **Stack-based**: All formatting uses stack allocation, avoiding heap overhead
2. **Zero-cost when disabled**: When the `logging` feature is disabled, all macros become no-ops
3. **Minimal dependencies**: Uses only `itoa` for integer formatting, falling back to `core::fmt` for other types
4. **Platform optimized**: Direct output to platform-specific channels (GHCB for SNP)

## Best Practices

1. **Use appropriate log levels**: Reserve `error` for actual errors, `debug` for development
2. **Implement DekoDebug carefully**: Avoid infinite recursion in custom implementations  
3. **Use conditional logging**: For expensive computations, use `log_if!` macro
4. **Memory dumps**: Use hex dumps sparingly as they can be verbose
5. **Feature gating**: Always disable logging in production builds

## Troubleshooting

### Common Issues

1. **Compilation errors with lexical**: The system falls back to `core::fmt` if lexical features are not available
2. **Missing output**: Ensure the platform (SNP/TDX) logging is properly initialized
3. **Macro visibility**: Import macros with `use deko_core::*;` to access all logging macros
4. **Verus integration**: All logging functions must be in `#[verifier::external_body]` blocks when used in verified code

### Debug Tips

1. Use `log_info!` to verify logging is working
2. Check platform initialization if no output appears
3. Use `deko_dbg!` for quick variable inspection
4. Combine hex dumps with structured debugging for complex data
