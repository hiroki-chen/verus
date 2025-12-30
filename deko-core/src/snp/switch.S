.code64
.pushsection .entry.text, "ax"

.globl __vmpl_switch
__vmpl_switch:
  // int __vmpl_switch(unsigned char target_vmpl)
  cmpl    $3, %edi
  ja      .Lend            // target_vmpl > 3!

  movl    $0x16, %eax
  movl    %edi, %edx
  movl    $0xc0010130, %ecx  // MSR_GHCB
  wrmsr

  rep; vmmcall

  ud2

  rdmsr
  andl   $0xfff, %eax
  cmpl   $0x17, %eax
  jz     .Lend
  movq   $0, %rax
  retq

.Lend:
  movq   $1, %rax // error.
  retq

.popsection
