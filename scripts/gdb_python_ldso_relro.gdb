set pagination off
set confirm off
set disassemble-next-line on
set breakpoint pending on

file /usr/bin/python3
set args -S -c 'print("hi")'

set environment GLIBC_TUNABLES glibc.rtld.dynamic_sort=2

starti

python
import gdb

inferior = gdb.selected_inferior()
maps = open(f"/proc/{inferior.pid}/maps").read().splitlines()
ldso_base = None
ldso_path = None

for line in maps:
    if "ld-linux-x86-64.so.2" in line and "r-xp" in line:
        start = int(line.split("-")[0], 16)
        ldso_base = start - 0x1000
        ldso_path = line.split()[-1]
        break

if ldso_base is None:
    raise gdb.GdbError("failed to locate ld-linux mapping base")

call_site = ldso_base + 0x1f240
fault_addr = ldso_base + 0x36a60

gdb.write(f"ld.so path: {ldso_path}\n")
gdb.write(f"ld.so base: 0x{ldso_base:x}\n")
gdb.write(f"call-site : 0x{call_site:x}\n")
gdb.write(f"relro addr : 0x{fault_addr:x}\n")

gdb.execute(f"set $ldso_base = (unsigned long long)0x{ldso_base:x}")
gdb.execute(f"set $ldso_call_site = (unsigned long long)0x{call_site:x}")
gdb.execute(f"set $ldso_relro_addr = (unsigned long long)0x{fault_addr:x}")

gdb.execute(f"break *0x{call_site:x}")
gdb.execute(f"awatch *(unsigned long long*)0x{fault_addr:x}")
gdb.execute("break mprotect")
gdb.execute(f"x/16gx 0x{fault_addr & ~0xff:x}")
end

commands 1
  silent
  printf "\n== call-site hit ==\n"
  printf "pc=%p\n", $pc
  x/6i $pc
  bt 6
  continue
end

commands 2
  silent
  printf "\n== tunable awatch hit ==\n"
  printf "pc=%p watched=%p\n", $pc, (void*)$ldso_relro_addr
  x/8gx (($ldso_relro_addr & ~0xfffUL) + 0xa40)
  x/8i $pc
  bt full
  continue
end

commands 3
  silent
  printf "\n== mprotect ==\n"
  printf "addr=%p len=%#lx prot=%#lx\n", (void*)$rdi, (unsigned long)$rsi, (unsigned long)$rdx
  if ((unsigned long)$rdi == ((unsigned long)$ldso_relro_addr & ~0xfffUL))
    printf "== target relro page before mprotect ==\n"
    x/8gx (($ldso_relro_addr & ~0xfffUL) + 0xa40)
  end
  bt 6
  continue
end

continue
