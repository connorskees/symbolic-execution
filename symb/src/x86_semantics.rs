// ! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

use iced_x86::{Code, Decoder, Instruction as x86Instruction, Mnemonic, Register};

use ir::{Instruction, InstructionIdx, MemoryAccess, Operand};
use ir_translator::AstBuilder;

// #include <triton/cpuSize.hpp>
// #include <triton/exceptions.hpp>
// #include <triton/x86Semantics.hpp>
// #include <triton/x86Specifications.hpp>
// #include <triton/astContext.hpp>

mod triton {
    pub mod arch {
        pub mod x86 {
            pub const ID_PREFIX_REPNE: u32 = 0;
        }
    }
}

/* \page SMT_Semantics_Supported_page SMT Semantics Supported
    \brief [**internal**] All information about the supported semantics.

- \ref SMT_aarch64_Semantics_Supported_page
- \ref SMT_arm32_Semantics_Supported_page
- \ref SMT_x86_Semantics_Supported_page

*/

/* \page SMT_x86_Semantics_Supported_page x86 and x86-64 SMT semantics supported
    \brief [**internal**] List of the supported semantics for the x86 and x86-64 architectures.


Mnemonic                     | Extensions | Description
-----------------------------|------------|------------
AAA                          |            | ASCII Adjust After Addition
AAD                          |            | ASCII Adjust AX Before Division
AAM                          |            | ASCII Adjust AX After Multiply
AAS                          |            | ASCII Adjust AL After Subtraction
ADC                          |            | Add with Carry
ADCX                         | adx        | Unsigned Integer Addition of Two Operands with Carry Flag
ADD                          |            | Add
AND                          |            | Logical AND
ANDN                         | bmi1       | Logical AND NOT
ANDNPD                       | sse2       | Bitwise Logical AND NOT of Packed Double-Precision Floating-Point Values
ANDNPS                       | sse1       | Bitwise Logical AND NOT of Packed Single-Precision Floating-Point Values
ANDPD                        | sse2       | Bitwise Logical AND of Packed Double-Precision Floating-Point Values
ANDPS                        | sse1       | Bitwise Logical AND of Packed Single-Precision Floating-Point Values
BEXTR                        | bmi1/tbm   | Bit Field Extract
BLSI                         | bmi1       | Extract Lowest Set Isolated Bit
BLSMSK                       | bmi1       | Get Mask Up to Lowest Set Bit
BLSR                         | bmi1       | Reset Lowest Set Bit
BSF                          |            | Bit Scan Forward
BSR                          |            | Bit Scan Reverse
BSWAP                        |            | Byte Swap
BT                           |            | Bit Test
BTC                          |            | Bit Test and Complement
BTR                          |            | Bit Test and Reset
BTS                          |            | Bit Test and Set
CALL                         |            | Call Procedure
CBW                          |            | Convert byte (al) to word (ax)
CDQ                          |            | Convert dword (eax) to qword (edx:eax)
CDQE                         |            | Convert dword (eax) to qword (rax)
CLC                          |            | Clear Carry Flag
CLD                          |            | Clear Direction Flag
CLFLUSH                      | sse2       | Flush Cache Line
CLI                          |            | Clear Interrupt Flag
CLTS                         |            | Clear Task-Switched Flag in CR0
CMC                          |            | Complement Carry Flag
CMOVA                        |            | Move if not below
CMOVAE                       |            | Move if not below or equal
CMOVB                        |            | Move if below
CMOVBE                       |            | Move if below or equal
CMOVE                        |            | Move if zero
CMOVG                        |            | Move if not less
CMOVGE                       |            | Move if not less or equal
CMOVL                        |            | Move if less
CMOVLE                       |            | Move if less or equal
CMOVNE                       |            | Move if not zero
CMOVNO                       |            | Move if not overflow
CMOVNP                       |            | Move if not parity
CMOVNS                       |            | Move if not sign
CMOVO                        |            | Move if overflow
CMOVP                        |            | Move if parity
CMOVS                        |            | Move if sign
CMP                          |            | Compare Two Operands
CMPSB                        |            | Compare byte at address
CMPSD                        |            | Compare doubleword at address
CMPSQ                        |            | Compare quadword at address
CMPSW                        |            | Compare word at address
CMPXCHG                      |            | Compare and Exchange
CMPXCHG16B                   |            | Compare and Exchange 16 Bytes
CMPXCHG8B                    |            | Compare and Exchange 8 Bytes
CPUID                        |            | CPU Identification
CQO                          |            | Convert qword (rax) to oword (rdx:rax)
CWD                          |            | Convert word (ax) to dword (dx:ax)
CWDE                         |            | Convert word (ax) to dword (eax)
DEC                          |            | Decrement by 1
DIV                          |            | Unsigned Divide
ENDBR32                      |            | No Operation
ENDBR64                      |            | No Operation
EXTRACTPS                    | sse4.1     | Extract Packed Single Precision Floating-Point Value
IDIV                         |            | Signed Divide
IMUL                         |            | Signed Multiply
INC                          |            | Increment by 1
INVD                         |            | Invalidate Internal Caches
INVLPG                       |            | Invalidate TLB Entry
JA                           |            | Jump if not below (Jump if above)
JAE                          |            | Jump if not below or equal (Jump if above or equal)
JB                           |            | Jump if below
JBE                          |            | Jump if below or equal
JCXZ                         |            | Jump if cx is zero
JE                           |            | Jump if zero (Jump if equal)
JECXZ                        |            | Jump if ecx is zero
JG                           |            | Jump if not less or equal (Jump if greater)
JGE                          |            | Jump if not less (Jump if not less)
JL                           |            | Jump if less
JLE                          |            | Jump if less or equal
JMP                          |            | Jump
JNE                          |            | Jump if not equal
JNO                          |            | Jump if not overflow
JNP                          |            | Jump if not parity
JNS                          |            | Jump if not sign
JO                           |            | Jump if overflow
JP                           |            | Jump if parity
JRCXZ                        |            | Jump if rcx is zero
JS                           |            | Jump if sign
LAHF                         |            | Load Status Flags into AH Register
LDDQU                        | sse3       | Load Unaligned Integer 128 Bits
LDMXCSR                      | sse1       | Load MXCSR Register
LEA                          |            | Load Effective Address
LEAVE                        |            | High Level Procedure Exit
LFENCE                       | sse2       | Load Fence
LODSB                        |            | Load byte at address
LODSD                        |            | Load doubleword at address
LODSQ                        |            | Load quadword at address
LODSW                        |            | Load word at address
LOOP                         |            | Loop According to ECX Counter
LZCNT                        |            | Count the Number of Leading Zero Bits
FXRSTOR                      | sse1       | Restore the x87 FPU, MMX, XMM, and MXCSR register state from m512byte
FXRSTOR64                    | sse1       | Restore the x87 FPU, MMX, XMM, and MXCSR register state from m512byte (REX.W = 1)
FXSAVE                       | sse1       | Save the x87 FPU, MMX, XMM, and MXCSR register state to m512byte
FXSAVE64                     | sse1       | Save the x87 FPU, MMX, XMM, and MXCSR register state to m512byte (REX.W = 1)
INT3                         |            | Generate breakpoint trap.
MFENCE                       | sse2       | Memory Fence
MOV                          |            | Move
MOVABS                       |            | Move
MOVAPD                       | sse2       | Move Aligned Packed Double-Precision Floating-Point Values
MOVAPS                       | sse1       | Move Aligned Packed Single-Precision Floating-Point Values
MOVBE                        | mmx/sse2   | Move Data After Swapping Bytes
MOVD                         | mmx/sse2   | Move Doubleword
MOVDDUP                      | sse3       | Move One Double-FP and Duplicate
MOVDQ2Q                      | sse2       | Move Quadword from XMM to MMX Technology Register
MOVDQA                       | sse2       | Move Aligned Double Quadword
MOVDQU                       | sse2       | Move Unaligned Double Quadword
MOVHLPS                      | sse1       | Move Packed Single-Precision Floating-Point Values High to Low
MOVHPD                       | sse2       | Move High Packed Double-Precision Floating-Point Values
MOVHPS                       | sse1       | Move High Packed Single-Precision Floating-Point Values
MOVLHPS                      | sse1       | Move Packed Single-Precision Floating-Point Values Low to High
MOVLPD                       | sse2       | Move Low Packed Double-Precision Floating-Point Values
MOVLPS                       | sse1       | Move Low Packed Single-Precision Floating-Point Values
MOVMSKPD                     | sse2       | Extract Packed Double-Precision Floating-Point Sign Mask
MOVMSKPS                     | sse1       | Extract Packed Single-Precision Floating-Point Sign Mask
MOVNTDQ                      | sse2       | Store Double Quadword Using Non-Temporal Hint
MOVNTI                       | sse2       | Store Doubleword Using Non-Temporal Hint
MOVNTPD                      | sse2       | Store Packed Double-Precision Floating-Point Values Using Non-Temporal Hint
MOVNTPS                      | sse1       | Store Packed Single-Precision Floating-Point Values Using Non-Temporal Hint
MOVNTQ                       | sse1       | Store of Quadword Using Non-Temporal Hint
MOVQ                         | mmx/sse2   | Move Quadword
MOVQ2DQ                      | sse2       | Move Quadword from MMX Technology to XMM Register
MOVSB                        |            | Move byte at address
MOVSD                        |            | Move doubleword at address
MOVSHDUP                     | sse3       | Move Packed Single-FP High and Duplicate
MOVSLDUP                     | sse3       | Move Packed Single-FP Low and Duplicate
MOVSQ                        |            | Move quadword at address
MOVSW                        |            | Move word at address
MOVSX                        |            | Move with Sign-Extension
MOVSXD                       |            | Move with Sign-Extension
MOVUPD                       | see2       | Move Unaligned Packed Double-Precision Floating- Point Values
MOVUPS                       | see1       | Move Unaligned Packed Single-Precision Floating- Point Values
MOVSS                        | sse1       | Move Scalar Single-Precision Floating- Point Values
MOVZX                        |            | Move with Zero-Extend
MUL                          |            | Unsigned Multiply
MULX                         | bmi2       | Unsigned Multiply Without Affecting Flags
NEG                          |            | Two's Complement Negation
NOP                          |            | No Operation
NOT                          |            | One's Complement Negation
OR                           |            | Logical Inclusive OR
ORPD                         | sse2       | Bitwise Logical OR of Double-Precision Floating-Point Values
ORPS                         | sse1       | Bitwise Logical OR of Single-Precision Floating-Point Values
PACKUSWB                     | mmx/sse2   | Pack with Unsigned Saturation
PACKSSDW                     | mmx/sse2   | Pack with Signed Saturation
PACKSSWB                     | mmx/sse2   | Pack with Signed Saturation
PADDB                        | mmx/sse2   | Add packed byte integers
PADDD                        | mmx/sse2   | Add packed doubleword integers
PADDQ                        | mmx/sse2   | Add packed quadword integers
PADDW                        | mmx/sse2   | Add packed word integers
PALIGNR                      | sse3       | Packed Align Right
PAND                         | mmx/sse2   | Logical AND
PANDN                        | mmx/sse2   | Logical AND NOT
PAUSE                        | sse2       | Spin Loop Hint
PAVGB                        | sse1       | Average Packed Unsigned Byte Integers
PAVGW                        | sse1       | Average Packed Unsigned Word Integers
PCMPEQB                      | mmx/sse2   | Compare Packed Data for Equal (bytes)
PCMPEQD                      | mmx/sse2   | Compare Packed Data for Equal (dwords)
PCMPEQW                      | mmx/sse2   | Compare Packed Data for Equal (words)
PCMPGTB                      | mmx/sse2   | Compare Packed Data for Greater Than (bytes)
PCMPGTD                      | mmx/sse2   | Compare Packed Data for Greater Than (dwords)
PCMPGTW                      | mmx/sse2   | Compare Packed Data for Greater Than (words)
PEXTRB                       | sse4.1     | Extract Byte
PEXTRD                       | sse4.1     | Extract Dword
PEXTRQ                       | sse4.1     | Extract Qword
PEXTRW                       | sse4.1     | Extract Word
PINSRB                       | sse4.1     | Insert Byte
PINSRD                       | sse4.1     | Insert Dword
PINSRQ                       | sse4.1     | Insert Qword
PINSRW                       | sse2       | Insert Word
PMADDWD                      | mmx/sse2   | Multiply and Add Packed Integers
PMAXSB                       | sse4.1     | Maximum of Packed Signed Byte Integers
PMAXSD                       | sse4.1     | Maximum of Packed Signed Doubleword Integers
PMAXSW                       | sse1       | Maximum of Packed Signed Word Integers
PMAXUB                       | sse1       | Maximum of Packed Unsigned Byte Integers
PMAXUD                       | sse4.1     | Maximum of Packed Unsigned Doubleword Integers
PMAXUW                       | sse4.1     | Maximum of Packed Unsigned Word Integers
PMINSB                       | sse4.1     | Minimum of Packed Signed Byte Integers
PMINSD                       | sse4.1     | Minimum of Packed Signed Doubleword Integers
PMINSW                       | sse1       | Minimum of Packed Signed Word Integers
PMINUB                       | sse1       | Minimum of Packed Unsigned Byte Integers
PMINUD                       | sse4.1     | Minimum of Packed Unsigned Doubleword Integers
PMINUW                       | sse4.1     | Minimum of Packed Unsigned Word Integers
PMOVMSKB                     | sse1       | Move Byte Mask
PMOVSXBD                     | sse4.1     | Sign Extend 4 Packed Signed 8-bit Integers
PMOVSXBQ                     | sse4.1     | Sign Extend 2 Packed Signed 8-bit Integers
PMOVSXBW                     | sse4.1     | Sign Extend 8 Packed Signed 8-bit Integers
PMOVSXDQ                     | sse4.1     | Sign Extend 2 Packed Signed 32-bit Integers
PMOVSXWD                     | sse4.1     | Sign Extend 4 Packed Signed 16-bit Integers
PMOVSXWQ                     | sse4.1     | Sign Extend 2 Packed Signed 16-bit Integers
PMOVZXBD                     | sse4.1     | Zero Extend 4 Packed Signed 8-bit Integers
PMOVZXBQ                     | sse4.1     | Zero Extend 2 Packed Signed 8-bit Integers
PMOVZXBW                     | sse4.1     | Zero Extend 8 Packed Signed 8-bit Integers
PMOVZXDQ                     | sse4.1     | Zero Extend 2 Packed Signed 32-bit Integers
PMOVZXWD                     | sse4.1     | Zero Extend 4 Packed Signed 16-bit Integers
PMOVZXWQ                     | sse4.1     | Zero Extend 2 Packed Signed 16-bit Integers
PMULHW                       | sse4.1     | Multiply Packed Signed Integers and Store High Result
PMULLD                       | sse4.1     | Multiply Packed Integers and Store Low Result
PMULLW                       | sse4.1     | Multiply Packed Signed Integers and Store Low Result
PMULUDQ                      | sse2       | Multiply Unsigned Doubleword Integer
POP                          |            | Pop a Value from the Stack
POPCNT                       |            | Count Number of Bits Set to 1
POPAL/POPAD                  |            | Pop All General-Purpose Registers
POPF                         |            | Pop Stack into lower 16-bit of EFLAGS Register
POPFD                        |            | Pop Stack into EFLAGS Register
POPFQ                        |            | Pop Stack into RFLAGS Register
POR                          | mmx/sse2   | Bitwise Logical OR
PREFETCH                     | 3DNow      | Move data from m8 closer to the processor without expecting to write back
PREFETCHNTA                  | mmx/sse1   | Move data from m8 closer to the processor using NTA hint
PREFETCHT0                   | mmx/sse1   | Move data from m8 closer to the processor using T0 hint
PREFETCHT1                   | mmx/sse1   | Move data from m8 closer to the processor using T1 hint
PREFETCHT2                   | mmx/sse1   | Move data from m8 closer to the processor using T2 hint
PREFETCHW                    | 3DNow      | Move data from m8 closer to the processor in anticipation of a write
PSHUFB                       | sse3       | Shuffle bytes according to contents
PSHUFD                       | sse2       | Shuffle Packed Doublewords
PSHUFHW                      | sse2       | Shuffle Packed High Words
PSHUFLW                      | sse2       | Shuffle Packed Low Words
PSHUFW                       | sse1       | Shuffle Packed Words
PSLLD                        | mmx/ssed2  | Shift Doubleword Left Logical
PSLLDQ                       | sse2       | Shift Double Quadword Left Logical
PSLLQ                        | mmx/ssed2  | Shift Quadword Left Logical
PSLLW                        | mmx/ssed2  | Shift Word Left Logical
PSRAD                        | mmx/ssed2  | Shift Packed Doubleword Right Arithmetic
PSRAW                        | mmx/ssed2  | Shift Packed Word Right Arithmetic
PSRLD                        | sse2       | Shift Packed Doubleword Right Logical
PSRLDQ                       | sse2       | Shift Double Quadword Right Logical
PSRLQ                        | sse2       | Shift Quadword Right Logical
PSRLW                        | sse2       | Shift Word Right Logical
PSUBB                        | mmx/sse2   | Subtract packed byte integers
PSUBD                        | mmx/sse2   | Subtract packed doubleword integers
PSUBQ                        | mmx/sse2   | Subtract packed quadword integers
PSUBW                        | mmx/sse2   | Subtract packed word integers
PTEST                        | sse4.1     | Logical Compare
PUNPCKHBW                    | mmx,sse2   | Unpack High Data (Unpack and interleave high-order bytes)
PUNPCKHDQ                    | mmx,sse2   | Unpack High Data (Unpack and interleave high-order doublewords)
PUNPCKHQDQ                   | sse2       | Unpack High Data (Unpack and interleave high-order quadwords)
PUNPCKHWD                    | mmx,sse2   | Unpack High Data (Unpack and interleave high-order words)
PUNPCKLBW                    | mmx,sse2   | Unpack Low Data (Unpack and interleave low-order bytes)
PUNPCKLDQ                    | mmx,sse2   | Unpack Low Data (Unpack and interleave low-order doublewords)
PUNPCKLQDQ                   | sse2       | Unpack Low Data (Unpack and interleave low-order quadwords)
PUNPCKLWD                    | mmx,sse2   | Unpack Low Data (Unpack and interleave low-order words)
PUSH                         |            | Push a Value onto the Stack
PUSHAL/PUSHAD                |            | Push All General-Purpose Registers
PUSHFD                       |            | Push EFLAGS Register onto the Stack
PUSHFQ                       |            | Push RFLAGS Register onto the Stack
PXOR                         | mmx/sse2   | Logical Exclusive OR
RCL                          |            | Rotate Left with Carry
RCR                          |            | Rotate Right with Carry
RDTSC                        |            | Read Time-Stamp Counter
RET                          |            | Return from Procedure
ROL                          |            | Rotate Left
ROR                          |            | Rotate Right
RORX                         | bmi2       | Rotate Right Logical Without Affecting Flags
SAHF                         |            | Store AH into Flags
SAL                          |            | Shift Left
SAR                          |            | Shift Right Signed
SARX                         | bmi2       | Shift arithmetic right without affecting flags
SBB                          |            | Integer Subtraction with Borrow
SCASB                        |            | Scan byte at address
SCASD                        |            | Scan doubleword at address
SCASQ                        |            | Scan quadword at address
SCASW                        |            | Scan word at address
SETA                         |            | Set byte if above
SETAE                        |            | Set byte if above or equal
SETB                         |            | Set byte if below
SETBE                        |            | Set byte if below or equal
SETE                         |            | Set byte if zero
SETG                         |            | Set byte if greater
SETGE                        |            | Set byte if greater or equal
SETL                         |            | Set byte if less
SETLE                        |            | Set byte if less or equal
SETNE                        |            | Set byte if not zero
SETNO                        |            | Set byte if not overflow
SETNP                        |            | Set byte if not parity
SETNS                        |            | Set byte if not sign
SETO                         |            | Set byte if overflow
SETP                         |            | Set byte if parity
SETS                         |            | Set byte if sign
SFENCE                       | sse1       | Store Fence
SHL                          |            | Shift Left
SHLD                         |            | Double-precision Shift Left
SHLX                         | bmi2       | Shift Logical Left Without Affecting Flags
SHR                          |            | Shift Right Unsigned
SHRD                         |            | Double Precision Shift Right
SHRX                         | bmi2       | Shift Logical Right Without Affecting Flags
STC                          |            | Set Carry Flag
STD                          |            | Set Direction Flag
STI                          |            | Set Interrupt Flag
STMXCSR                      | sse1       | Store MXCSR Register State
STOSB                        |            | Store byte at address
STOSD                        |            | Store doubleword at address
STOSQ                        |            | Store quadword at address
STOSW                        |            | Store word at address
SUB                          |            | Subtract
SYSCALL                      |            | Fast System Call
SYSENTER                     |            | Fast System Call
TEST                         |            | Logical Compare
TZCNT                        | bmi1       | Count the Number of Trailing Zero Bits
UNPCKHPD                     | sse2       | Unpack and Interleave High Packed Double- Precision Floating-Point Values
UNPCKHPS                     | sse1       | Unpack and Interleave High Packed Single-Precision Floating-Point Values
UNPCKLPD                     | sse2       | Unpack and Interleave Low Packed Double-Precision Floating-Point Values
UNPCKLPS                     | sse1       | Unpack and Interleave Low Packed Single-Precision Floating-Point Values
VEXTRACTI128                 | avx2       | VEX Extract Packed Integer Values
VMOVD                        | avx        | VEX Move Doubleword
VMOVDQA                      | avx        | VEX Move aligned packed integer values
VMOVDQU                      | avx        | VEX Move unaligned packed integer values
VMOVNTDQ                     | avx        | VEX Store Double Quadword Using Non-Temporal Hint
VMOVQ                        | avx        | VEX Move Quadword
VMOVSD                       | avx        | VEX Move or Merge Scalar Double-Precision Floating-Point Value
VMOVAPS                      | avx        | VEX Move Aligned Packed Single-Precision Floating-Point Values
VMOVUPS                      | avx        | VEX Move Unaligned Packed Single-Precision Floating-Point Values
VPACKUSWB                    | avx/avx2   | VEX Pack with Unsigned Saturation
VPACKSSDW                    | avx/avx2   | VEX Pack with Signed Saturation
VPACKSSWB                    | avx/avx2   | VEX Pack with Signed Saturation
VPADDB                       | avx/avx2   | VEX Add Packed Byte Integers
VPADDD                       | avx/avx2   | VEX Add Packed Doubleword Integers
VPADDW                       | avx/avx2   | VEX Add Packed Word Integers
VPAND                        | avx/avx2   | VEX Logical AND
VPANDN                       | avx/avx2   | VEX Logical AND NOT
VPERM2I128                   | avx2       | VEX Permute Integer Values
VPERMQ                       | avx2       | VEX Qwords Element Permutation
VPEXTRB                      | avx/avx2   | VEX Extract Byte
VPEXTRD                      | avx/avx2   | VEX Extract Dword
VPEXTRQ                      | avx/avx2   | VEX Extract Qword
VPEXTRW                      | avx/avx2   | VEX Extract Word
VPBROADCASTB                 | avx2       | VEX Load Byte Integer and broadcast
VPCMPEQB                     | avx/avx2   | VEX Compare packed Bytes for equality
VPCMPEQD                     | avx/avx2   | VEX Compare packed Doublewords for equality
VPCMPEQQ                     | avx/avx2   | VEX Compare packed Quadwords for equality
VPCMPEQW                     | avx/avx2   | VEX Compare packed Words for equality
VPCMPGTB                     | avx/avx2   | VEX Compare Packed Bytes for Greater Than
VPCMPGTD                     | avx/avx2   | VEX Compare Packed Doublewords for Greater Than
VPCMPGTW                     | avx/avx2   | VEX Compare Packed Words for Greater Than
VPMADDWD                     | avx/avx    | VEX Multiply and Add Packed Integers
VPMOVMSKB                    | avx/avx2   | VEX Move Byte Mask
VPMINUB                      | avx/avx2   | VEX Minimum of Packed Unsigned Byte Integers
VPMULHW                      | avx/avx2   | VEX Multiply Packed Signed Integers and Store High Result
VPMULLW                      | avx/avx2   | VEX Multiply Packed Signed Integers and Store Low Result
VPOR                         | avx/avx2   | VEX Logical OR
VPSHUFD                      | avx/avx2   | VEX Shuffle Packed Doublewords
VPSIGNW                      | avx/avx2   | VEX Packed SIGN
VPSLLDQ                      | avx/avx2   | VEX Shift Packed Double Quadword Left Logical
VPSLLW                       | avx/avx2   | VEX Shift Packed Word Left Logical
VPSRAD                       | avx/avx2   | VEX Shift Packed Doubleword Right Arithmetic
VPSRAW                       | avx/avx2   | VEX Shift Packed Word Right Arithmetic
VPSRLDQ                      | avx/avx2   | VEX Shift Packed Double Quadword Right Logical
VPSRLW                       | avx/avx2   | VEX Shift Packed Word Right Logical
VPSUBB                       | avx/avx2   | VEX Subtract packed Byte integers
VPSUBD                       | avx/avx2   | VEX Subtract packed Doubleword integers
VPSUBQ                       | avx/avx2   | VEX Subtract packed Quadword integers
VPSUBW                       | avx/avx2   | VEX Subtract packed Word integers
VPTEST                       | avx        | VEX Logical Compare
VPUNPCKHBW                   | avx/avx2   | VEX Unpack High Data (Unpack and interleave high-order bytes)
VPUNPCKHDQ                   | avx/avx2   | VEX Unpack High Data (Unpack and interleave high-order doublewords)
VPUNPCKHQDQ                  | avx/avx2   | VEX Unpack High Data (Unpack and interleave high-order quadwords)
VPUNPCKHWD                   | avx/avx2   | VEX Unpack High Data (Unpack and interleave high-order words)
VPUNPCKLBW                   | avx/avx2   | VEX Unpack Low Data (Unpack and interleave low-order bytes)
VPUNPCKLDQ                   | avx/avx2   | VEX Unpack Low Data (Unpack and interleave low-order doublewords)
VPUNPCKLQDQ                  | avx/avx2   | VEX Unpack Low Data (Unpack and interleave low-order quadwords)
VPUNPCKLWD                   | avx/avx2   | VEX Unpack Low Data (Unpack and interleave low-order words)
VPXOR                        | avx/avx2   | VEX Logical XOR
VXORPS                       | avx        | VEX Bitwise Logical XOR for Single-Precision Floating-Point Values
WAIT                         |            | Wait
WBINVD                       |            | Write Back and Invalidate Cache
XADD                         |            | Exchange and Add
XCHG                         |            | Exchange Register/Memory with Register
XOR                          |            | Logical Exclusive OR
XORPD                        | sse2       | Bitwise Logical XOR for Double-Precision Floating-Point Values
XORPS                        | sse1       | Bitwise Logical XOR for Single-Precision Floating-Point Values

*/

pub(crate) struct x86Semantics {
    ast_ctxt: AstBuilder,
    architecture: Architecture,
    // symbolicEngine: SymbolicEngine,
    // taintEngine: TaintEngine,
    // modes: SharedModes,
}

struct SymbolicEngine {}

impl SymbolicEngine {
    fn getOperandAst(&self, inst: x86Instruction, st0: Operand) -> Operand {
        todo!()
    }

    // fn createSymbolicExpression()
}

#[derive(Debug, Clone, Copy)]
struct OperandWrapper(x86Instruction, u8);

impl OperandWrapper {
    fn get_bit_size(&self) -> u32 {
        match self.0.op_kind(self.1 as u32) {
            iced_x86::OpKind::Register => self.0.op_register(self.1 as u32).size() as u32 * 8,
            iced_x86::OpKind::NearBranch16 => 16,
            iced_x86::OpKind::NearBranch32 => 32,
            iced_x86::OpKind::NearBranch64 => 64,
            iced_x86::OpKind::FarBranch16 => 16,
            iced_x86::OpKind::FarBranch32 => 32,
            iced_x86::OpKind::Immediate8 => 8,
            iced_x86::OpKind::Immediate8_2nd => 8,
            iced_x86::OpKind::Immediate16 => 16,
            iced_x86::OpKind::Immediate32 => 32,
            iced_x86::OpKind::Immediate64 => 64,
            iced_x86::OpKind::Immediate8to16 => 16,
            iced_x86::OpKind::Immediate8to32 => 32,
            iced_x86::OpKind::Immediate8to64 => 64,
            iced_x86::OpKind::Immediate32to64 => 64,
            iced_x86::OpKind::MemorySegSI => todo!(),
            iced_x86::OpKind::MemorySegESI => todo!(),
            iced_x86::OpKind::MemorySegRSI => todo!(),
            iced_x86::OpKind::MemorySegDI => todo!(),
            iced_x86::OpKind::MemorySegEDI => todo!(),
            iced_x86::OpKind::MemorySegRDI => todo!(),
            iced_x86::OpKind::MemoryESDI => todo!(),
            iced_x86::OpKind::MemoryESEDI => todo!(),
            iced_x86::OpKind::MemoryESRDI => todo!(),
            iced_x86::OpKind::Memory => self.0.memory_base().size() as u32 * 8,
        }
    }

    fn get_low(&self) -> u32 {
        // todo!()
        0
    }

    fn get_high(&self) -> u32 {
        // todo!()
        0
    }
}

pub struct Architecture {
    is_64_bit: bool,
}

impl Architecture {
    pub fn new() -> Self {
        Architecture { is_64_bit: true }
    }

    fn get_stack_pointer(&self) -> Register {
        if self.is_64_bit {
            Register::RSP
        } else {
            Register::ESP
        }
    }

    fn get_program_counter(&self) -> Register {
        if self.is_64_bit {
            Register::RIP
        } else {
            Register::EIP
        }
    }

    fn is_register_valid(&self, reg: Register) -> bool {
        true
        // reg.base()
        // let is_flag = register >= Register::AC && register <= Register::FZ;
        // bool isInvalid = register != register_e.ID_REG_INVALID;

        //     bool isFlag = (register >= register_e.ID_REG_X86_AC && register <= register_e.ID_REG_X86_FZ) ? true : false;

        //     return isInvalid || isFlag;
    }
}

struct BitSizes {}

impl BitSizes {
    const FLAG: u32 = 1;
    const BYTE: u32 = 8;
    const WORD: u32 = 16;
    const DWORD: u32 = 32;
    const QWORD: u32 = 64;
    const FWORD: u32 = 80;
    const DQWORD: u32 = 128;
    const QQWORD: u32 = 256;
    const DQQWORD: u32 = 512;
}
struct ByteSizes {}

impl ByteSizes {
    const BYTE: u32 = BitSizes::BYTE / 8;
    const WORD: u32 = BitSizes::WORD / 8;
    const DWORD: u32 = BitSizes::DWORD / 8;
    const QWORD: u32 = BitSizes::QWORD / 8;
    const FWORD: u32 = BitSizes::FWORD / 8;
    const DQWORD: u32 = BitSizes::DQWORD / 8;
    const QQWORD: u32 = BitSizes::QQWORD / 8;
    const DQQWORD: u32 = BitSizes::DQQWORD / 8;
}

struct TaintEngine {}
struct SharedModes {}

impl x86Semantics {
    pub fn new(
        architecture: Architecture,
        // symbolicEngine: SymbolicEngine,
        // taintEngine: TaintEngine,
        // modes: SharedModes,
        ast_ctxt: AstBuilder,
    ) -> Self {
        Self {
            architecture,
            // symbolicEngine,
            // taintEngine,
            // modes,
            ast_ctxt,
        }

        // self.architecture    = architecture;
        // self.exception       = triton::arch::NO_FAULT;
        // self.symbolicEngine  = symbolicEngine;
        // self.taintEngine     = taintEngine;

        // if (architecture == nullptr)
        //   todo!(r#"triton::exceptions::Semantics("x86Semantics::x86Semantics(): The architecture API must be defined.");"#);

        // if (self.symbolicEngine == nullptr)
        //   todo!(r#"triton::exceptions::Semantics("x86Semantics::x86Semantics(): The symbolic engine API must be defined.");"#);

        // if (self.taintEngine == nullptr)
        //   todo!(r#"triton::exceptions::Semantics("x86Semantics::x86Semantics(): The taint engines API must be defined.");"#);
    }

    pub fn build_semantics(&mut self, inst: x86Instruction) -> bool {
        // self.exception = triton::arch::NO_FAULT;
        match inst.mnemonic() {
            //   Mnemonic::Aaa => self.aaa_s(inst),
            //   Mnemonic::Aad => self.aad_s(inst),
            //   Mnemonic::Aam => self.aam_s(inst),
            //   Mnemonic::Aas => self.aas_s(inst),
            //   Mnemonic::Adc => self.adc_s(inst),
            //   Mnemonic::Adcx => self.adcx_s(inst),
            //   Mnemonic::Add => self.add_s(inst),
            //   Mnemonic::And => self.and_s(inst),
            //   Mnemonic::Andn => self.andn_s(inst),
            //   Mnemonic::Andnpd => self.andnpd_s(inst),
            //   Mnemonic::Andnps => self.andnps_s(inst),
            //   Mnemonic::Andpd => self.andpd_s(inst),
            //   Mnemonic::Andps => self.andps_s(inst),
            //   Mnemonic::Bextr => self.bextr_s(inst),
            //   Mnemonic::Blsi => self.blsi_s(inst),
            //   Mnemonic::Blsmsk => self.blsmsk_s(inst),
            //   Mnemonic::Blsr => self.blsr_s(inst),
            //   Mnemonic::Bsf => self.bsf_s(inst),
            //   Mnemonic::Bsr => self.bsr_s(inst),
            //   Mnemonic::Bswap => self.bswap_s(inst),
            //   Mnemonic::Bt => self.bt_s(inst),
            //   Mnemonic::Btc => self.btc_s(inst),
            //   Mnemonic::Btr => self.btr_s(inst),
            //   Mnemonic::Bts => self.bts_s(inst),
            //   Mnemonic::Call => self.call_s(inst),
            //   Mnemonic::Cbw => self.cbw_s(inst),
            //   Mnemonic::Cdq => self.cdq_s(inst),
            //   Mnemonic::Cdqe => self.cdqe_s(inst),
            //   Mnemonic::Clc => self.clc_s(inst),
            //   Mnemonic::Cld => self.cld_s(inst),
            //   Mnemonic::Clflush => self.clflush_s(inst),
            //   Mnemonic::Clts => self.clts_s(inst),
            //   Mnemonic::Cli => self.cli_s(inst),
            //   Mnemonic::Cmc => self.cmc_s(inst),
            //   Mnemonic::Cmova => self.cmova_s(inst),
            //   Mnemonic::Cmovae => self.cmovae_s(inst),
            //   Mnemonic::Cmovb => self.cmovb_s(inst),
            //   Mnemonic::Cmovbe => self.cmovbe_s(inst),
            //   Mnemonic::Cmove => self.cmove_s(inst),
            //   Mnemonic::Cmovg => self.cmovg_s(inst),
            //   Mnemonic::Cmovge => self.cmovge_s(inst),
            //   Mnemonic::Cmovl => self.cmovl_s(inst),
            //   Mnemonic::Cmovle => self.cmovle_s(inst),
            //   Mnemonic::Cmovne => self.cmovne_s(inst),
            //   Mnemonic::Cmovno => self.cmovno_s(inst),
            //   Mnemonic::Cmovnp => self.cmovnp_s(inst),
            //   Mnemonic::Cmovns => self.cmovns_s(inst),
            //   Mnemonic::Cmovo => self.cmovo_s(inst),
            //   Mnemonic::Cmovp => self.cmovp_s(inst),
            //   Mnemonic::Cmovs => self.cmovs_s(inst),
            //   Mnemonic::Cmp => self.cmp_s(inst),
            //   Mnemonic::Cmpsb => self.cmpsb_s(inst),
            //   Mnemonic::Cmpsd => self.cmpsd_s(inst),
            //   Mnemonic::Cmpsq => self.cmpsq_s(inst),
            //   Mnemonic::Cmpsw => self.cmpsw_s(inst),
            //   Mnemonic::Cmpxchg => self.cmpxchg_s(inst),
            //   Mnemonic::Cmpxchg16b => self.cmpxchg16b_s(inst),
            //   Mnemonic::Cmpxchg8b => self.cmpxchg8b_s(inst),
            //   Mnemonic::Cpuid => self.cpuid_s(inst),
            //   Mnemonic::Cqo => self.cqo_s(inst),
            //   Mnemonic::Cwd => self.cwd_s(inst),
            //   Mnemonic::Cwde => self.cwde_s(inst),
            //   Mnemonic::Dec => self.dec_s(inst),
            //   Mnemonic::Div => self.div_s(inst),
            //   Mnemonic::Endbr32 => self.endbr32_s(inst),
            //   Mnemonic::Endbr64 => self.endbr64_s(inst),
            //   Mnemonic::Extractps => self.extractps_s(inst),
            //   Mnemonic::Fxrstor64 => self.fxrstor64_s(inst),
            //   Mnemonic::Fxrstor => self.fxrstor_s(inst),
            //   Mnemonic::Fxsave64 => self.fxsave64_s(inst),
            //   Mnemonic::Fxsave => self.fxsave_s(inst),
            //   Mnemonic::Idiv => self.idiv_s(inst),
            //   Mnemonic::Imul => self.imul_s(inst),
            //   Mnemonic::Inc => self.inc_s(inst),
            //   Mnemonic::Invd => self.invd_s(inst),
            //   Mnemonic::Invlpg => self.invlpg_s(inst),
            //   Mnemonic::Ja => self.ja_s(inst),
            //   Mnemonic::Jae => self.jae_s(inst),
            //   Mnemonic::Jb => self.jb_s(inst),
            //   Mnemonic::Jbe => self.jbe_s(inst),
            //   Mnemonic::Jcxz => self.jcxz_s(inst),
            //   Mnemonic::Je => self.je_s(inst),
            //   Mnemonic::Jecxz => self.jecxz_s(inst),
            //   Mnemonic::Jg => self.jg_s(inst),
            //   Mnemonic::Jge => self.jge_s(inst),
            //   Mnemonic::Jl => self.jl_s(inst),
            //   Mnemonic::Jle => self.jle_s(inst),
            //   Mnemonic::Jmp => self.jmp_s(inst),
            //   Mnemonic::Jne => self.jne_s(inst),
            //   Mnemonic::Jno => self.jno_s(inst),
            //   Mnemonic::Jnp => self.jnp_s(inst),
            //   Mnemonic::Jns => self.jns_s(inst),
            //   Mnemonic::Jo => self.jo_s(inst),
            //   Mnemonic::Jp => self.jp_s(inst),
            //   Mnemonic::Jrcxz => self.jrcxz_s(inst),
            //   Mnemonic::Js => self.js_s(inst),
            //   Mnemonic::Lahf => self.lahf_s(inst),
            //   Mnemonic::Lddqu => self.lddqu_s(inst),
            //   Mnemonic::Ldmxcsr => self.ldmxcsr_s(inst),
            Mnemonic::Lea => self.lea_s(inst),
            //   Mnemonic::Leave => self.leave_s(inst),
            //   Mnemonic::Lfence => self.lfence_s(inst),
            //   Mnemonic::Lodsb => self.lodsb_s(inst),
            //   Mnemonic::Lodsd => self.lodsd_s(inst),
            //   Mnemonic::Lodsq => self.lodsq_s(inst),
            //   Mnemonic::Lodsw => self.lodsw_s(inst),
            //   Mnemonic::Loop => self.loop_s(inst),
            //   Mnemonic::Lzcnt => self.lzcnt_s(inst),
            //   Mnemonic::Int3 => self.int3_s(inst),
            //   Mnemonic::Mfence => self.mfence_s(inst),
            Mnemonic::Mov => self.mov_s(inst),
            // //   Mnemonic::Movabs => self.movabs_s(inst),
            //   Mnemonic::Movapd => self.movapd_s(inst),
            //   Mnemonic::Movaps => self.movaps_s(inst),
            //   Mnemonic::Movbe => self.movbe_s(inst),
            //   Mnemonic::Movd => self.movd_s(inst),
            //   Mnemonic::Movddup => self.movddup_s(inst),
            //   Mnemonic::Movdq2q => self.movdq2q_s(inst),
            //   Mnemonic::Movdqa => self.movdqa_s(inst),
            //   Mnemonic::Movdqu => self.movdqu_s(inst),
            //   Mnemonic::Movhlps => self.movhlps_s(inst),
            //   Mnemonic::Movhpd => self.movhpd_s(inst),
            //   Mnemonic::Movhps => self.movhps_s(inst),
            //   Mnemonic::Movlhps => self.movlhps_s(inst),
            //   Mnemonic::Movlpd => self.movlpd_s(inst),
            //   Mnemonic::Movlps => self.movlps_s(inst),
            //   Mnemonic::Movmskpd => self.movmskpd_s(inst),
            //   Mnemonic::Movmskps => self.movmskps_s(inst),
            //   Mnemonic::Movntdq => self.movntdq_s(inst),
            //   Mnemonic::Movnti => self.movnti_s(inst),
            //   Mnemonic::Movntpd => self.movntpd_s(inst),
            //   Mnemonic::Movntps => self.movntps_s(inst),
            //   Mnemonic::Movntq => self.movntq_s(inst),
            //   Mnemonic::Movq2dq => self.movq2dq_s(inst),
            //   Mnemonic::Movq => self.movq_s(inst),
            //   Mnemonic::Movsb => self.movsb_s(inst),
            //   Mnemonic::Movsd => self.movsd_s(inst),
            //   Mnemonic::Movshdup => self.movshdup_s(inst),
            //   Mnemonic::Movsldup => self.movsldup_s(inst),
            //   Mnemonic::Movupd => self.movupd_s(inst),
            //   Mnemonic::Movups => self.movups_s(inst),
            //   Mnemonic::Movss => self.movss_s(inst),
            //   Mnemonic::Movsq => self.movsq_s(inst),
            //   Mnemonic::Movsw => self.movsw_s(inst),
            //   Mnemonic::Movsx => self.movsx_s(inst),
            //   Mnemonic::Movsxd => self.movsxd_s(inst),
            //   Mnemonic::Movzx => self.movzx_s(inst),
            //   Mnemonic::Mul => self.mul_s(inst),
            //   Mnemonic::Mulx => self.mulx_s(inst),
            //   Mnemonic::Neg => self.neg_s(inst),
            //   Mnemonic::Nop => self.nop_s(inst),
            //   Mnemonic::Not => self.not_s(inst),
            //   Mnemonic::Or => self.or_s(inst),
            //   Mnemonic::Orpd => self.orpd_s(inst),
            //   Mnemonic::Orps => self.orps_s(inst),
            //   Mnemonic::Packuswb => self.packuswb_s(inst),
            //   Mnemonic::Packssdw => self.packssdw_s(inst),
            //   Mnemonic::Packsswb => self.packsswb_s(inst),
            //   Mnemonic::Paddb => self.paddb_s(inst),
            //   Mnemonic::Paddd => self.paddd_s(inst),
            //   Mnemonic::Paddq => self.paddq_s(inst),
            //   Mnemonic::Paddw => self.paddw_s(inst),
            //   Mnemonic::Palignr => self.palignr_s(inst),
            //   Mnemonic::Pand => self.pand_s(inst),
            //   Mnemonic::Pandn => self.pandn_s(inst),
            //   Mnemonic::Pause => self.pause_s(inst),
            //   Mnemonic::Pavgb => self.pavgb_s(inst),
            //   Mnemonic::Pavgw => self.pavgw_s(inst),
            //   Mnemonic::Pcmpeqb => self.pcmpeqb_s(inst),
            //   Mnemonic::Pcmpeqd => self.pcmpeqd_s(inst),
            //   Mnemonic::Pcmpeqw => self.pcmpeqw_s(inst),
            //   Mnemonic::Pcmpgtb => self.pcmpgtb_s(inst),
            //   Mnemonic::Pcmpgtd => self.pcmpgtd_s(inst),
            //   Mnemonic::Pcmpgtw => self.pcmpgtw_s(inst),
            //   Mnemonic::Pextrb => self.pextrb_s(inst),
            //   Mnemonic::Pextrd => self.pextrd_s(inst),
            //   Mnemonic::Pextrq => self.pextrq_s(inst),
            //   Mnemonic::Pextrw => self.pextrw_s(inst),
            //   Mnemonic::Pinsrb => self.pinsrb_s(inst),
            //   Mnemonic::Pinsrd => self.pinsrd_s(inst),
            //   Mnemonic::Pinsrq => self.pinsrq_s(inst),
            //   Mnemonic::Pinsrw => self.pinsrw_s(inst),
            //   Mnemonic::Pmaddwd => self.pmaddwd_s(inst),
            //   Mnemonic::Pmaxsb => self.pmaxsb_s(inst),
            //   Mnemonic::Pmaxsd => self.pmaxsd_s(inst),
            //   Mnemonic::Pmaxsw => self.pmaxsw_s(inst),
            //   Mnemonic::Pmaxub => self.pmaxub_s(inst),
            //   Mnemonic::Pmaxud => self.pmaxud_s(inst),
            //   Mnemonic::Pmaxuw => self.pmaxuw_s(inst),
            //   Mnemonic::Pminsb => self.pminsb_s(inst),
            //   Mnemonic::Pminsd => self.pminsd_s(inst),
            //   Mnemonic::Pminsw => self.pminsw_s(inst),
            //   Mnemonic::Pminub => self.pminub_s(inst),
            //   Mnemonic::Pminud => self.pminud_s(inst),
            //   Mnemonic::Pminuw => self.pminuw_s(inst),
            //   Mnemonic::Pmovmskb => self.pmovmskb_s(inst),
            //   Mnemonic::Pmovsxbd => self.pmovsxbd_s(inst),
            //   Mnemonic::Pmovsxbq => self.pmovsxbq_s(inst),
            //   Mnemonic::Pmovsxbw => self.pmovsxbw_s(inst),
            //   Mnemonic::Pmovsxdq => self.pmovsxdq_s(inst),
            //   Mnemonic::Pmovsxwd => self.pmovsxwd_s(inst),
            //   Mnemonic::Pmovsxwq => self.pmovsxwq_s(inst),
            //   Mnemonic::Pmovzxbd => self.pmovzxbd_s(inst),
            //   Mnemonic::Pmovzxbq => self.pmovzxbq_s(inst),
            //   Mnemonic::Pmovzxbw => self.pmovzxbw_s(inst),
            //   Mnemonic::Pmovzxdq => self.pmovzxdq_s(inst),
            //   Mnemonic::Pmovzxwd => self.pmovzxwd_s(inst),
            //   Mnemonic::Pmovzxwq => self.pmovzxwq_s(inst),
            //   Mnemonic::Pmulhw => self.pmulhw_s(inst),
            //   Mnemonic::Pmulld => self.pmulld_s(inst),
            //   Mnemonic::Pmullw => self.pmullw_s(inst),
            //   Mnemonic::Pmuludq => self.pmuludq_s(inst),
            //   Mnemonic::Popcnt => self.popcnt_s(inst),
            //   Mnemonic::Pop => self.pop_s(inst),
            // //   Mnemonic::Popal => self.popal_s(inst),
            //   Mnemonic::Popf => self.popf_s(inst),
            //   Mnemonic::Popfd => self.popfd_s(inst),
            //   Mnemonic::Popfq => self.popfq_s(inst),
            //   Mnemonic::Por => self.por_s(inst),
            //   Mnemonic::Prefetch => self.prefetchx_s(inst),
            //   Mnemonic::Prefetchnta => self.prefetchx_s(inst),
            //   Mnemonic::Prefetcht0 => self.prefetchx_s(inst),
            //   Mnemonic::Prefetcht1 => self.prefetchx_s(inst),
            //   Mnemonic::Prefetcht2 => self.prefetchx_s(inst),
            //   Mnemonic::Prefetchw => self.prefetchx_s(inst),
            //   Mnemonic::Pshufb => self.pshufb_s(inst),
            //   Mnemonic::Pshufd => self.pshufd_s(inst),
            //   Mnemonic::Pshufhw => self.pshufhw_s(inst),
            //   Mnemonic::Pshuflw => self.pshuflw_s(inst),
            //   Mnemonic::Pshufw => self.pshufw_s(inst),
            //   Mnemonic::Pslld => self.pslld_s(inst),
            //   Mnemonic::Pslldq => self.pslldq_s(inst),
            //   Mnemonic::Psllq => self.psllq_s(inst),
            //   Mnemonic::Psllw => self.psllw_s(inst),
            //   Mnemonic::Psrad => self.psrad_s(inst),
            //   Mnemonic::Psraw => self.psraw_s(inst),
            //   Mnemonic::Psrld => self.psrld_s(inst),
            //   Mnemonic::Psrldq => self.psrldq_s(inst),
            //   Mnemonic::Psrlq => self.psrlq_s(inst),
            //   Mnemonic::Psrlw => self.psrlw_s(inst),
            //   Mnemonic::Psubb => self.psubb_s(inst),
            //   Mnemonic::Psubd => self.psubd_s(inst),
            //   Mnemonic::Psubq => self.psubq_s(inst),
            //   Mnemonic::Psubw => self.psubw_s(inst),
            //   Mnemonic::Ptest => self.ptest_s(inst),
            //   Mnemonic::Punpckhbw => self.punpckhbw_s(inst),
            //   Mnemonic::Punpckhdq => self.punpckhdq_s(inst),
            //   Mnemonic::Punpckhqdq => self.punpckhqdq_s(inst),
            //   Mnemonic::Punpckhwd => self.punpckhwd_s(inst),
            //   Mnemonic::Punpcklbw => self.punpcklbw_s(inst),
            //   Mnemonic::Punpckldq => self.punpckldq_s(inst),
            //   Mnemonic::Punpcklqdq => self.punpcklqdq_s(inst),
            //   Mnemonic::Punpcklwd => self.punpcklwd_s(inst),
            //   Mnemonic::Push => self.push_s(inst),
            // //   Mnemonic::Pushal => self.pushal_s(inst),
            //   Mnemonic::Pushfd => self.pushfd_s(inst),
            //   Mnemonic::Pushfq => self.pushfq_s(inst),
            //   Mnemonic::Pxor => self.pxor_s(inst),
            //   Mnemonic::Rcl => self.rcl_s(inst),
            //   Mnemonic::Rcr => self.rcr_s(inst),
            //   Mnemonic::Rdtsc => self.rdtsc_s(inst),
            //   Mnemonic::Ret => self.ret_s(inst),
            //   Mnemonic::Rol => self.rol_s(inst),
            //   Mnemonic::Ror => self.ror_s(inst),
            //   Mnemonic::Rorx => self.rorx_s(inst),
            //   Mnemonic::Sahf => self.sahf_s(inst),
            //   Mnemonic::Sal => self.shl_s(inst),
            //   Mnemonic::Sar => self.sar_s(inst),
            //   Mnemonic::Sarx => self.sarx_s(inst),
            //   Mnemonic::Sbb => self.sbb_s(inst),
            //   Mnemonic::Scasb => self.scasb_s(inst),
            //   Mnemonic::Scasd => self.scasd_s(inst),
            //   Mnemonic::Scasq => self.scasq_s(inst),
            //   Mnemonic::Scasw => self.scasw_s(inst),
            //   Mnemonic::Seta => self.seta_s(inst),
            //   Mnemonic::Setae => self.setae_s(inst),
            //   Mnemonic::Setb => self.setb_s(inst),
            //   Mnemonic::Setbe => self.setbe_s(inst),
            //   Mnemonic::Sete => self.sete_s(inst),
            //   Mnemonic::Setg => self.setg_s(inst),
            //   Mnemonic::Setge => self.setge_s(inst),
            //   Mnemonic::Setl => self.setl_s(inst),
            //   Mnemonic::Setle => self.setle_s(inst),
            //   Mnemonic::Setne => self.setne_s(inst),
            //   Mnemonic::Setno => self.setno_s(inst),
            //   Mnemonic::Setnp => self.setnp_s(inst),
            //   Mnemonic::Setns => self.setns_s(inst),
            //   Mnemonic::Seto => self.seto_s(inst),
            //   Mnemonic::Setp => self.setp_s(inst),
            //   Mnemonic::Sets => self.sets_s(inst),
            //   Mnemonic::Sfence => self.sfence_s(inst),
            //   Mnemonic::Shl => self.shl_s(inst),
            //   Mnemonic::Shld => self.shld_s(inst),
            //   Mnemonic::Shlx => self.shlx_s(inst),
            //   Mnemonic::Shr => self.shr_s(inst),
            //   Mnemonic::Shrd => self.shrd_s(inst),
            //   Mnemonic::Shrx => self.shrx_s(inst),
            //   Mnemonic::Stc => self.stc_s(inst),
            //   Mnemonic::Std => self.std_s(inst),
            //   Mnemonic::Sti => self.sti_s(inst),
            //   Mnemonic::Stmxcsr => self.stmxcsr_s(inst),
            //   Mnemonic::Stosb => self.stosb_s(inst),
            //   Mnemonic::Stosd => self.stosd_s(inst),
            //   Mnemonic::Stosq => self.stosq_s(inst),
            //   Mnemonic::Stosw => self.stosw_s(inst),
            Mnemonic::Sub => self.sub_s(inst),
            //   Mnemonic::Syscall => self.syscall_s(inst),
            //   Mnemonic::Sysenter => self.sysenter_s(inst),
            //   Mnemonic::Test => self.test_s(inst),
            //   Mnemonic::Tzcnt => self.tzcnt_s(inst),
            //   Mnemonic::Unpckhpd => self.unpckhpd_s(inst),
            //   Mnemonic::Unpckhps => self.unpckhps_s(inst),
            //   Mnemonic::Unpcklpd => self.unpcklpd_s(inst),
            //   Mnemonic::Unpcklps => self.unpcklps_s(inst),
            //   Mnemonic::Vextracti128 => self.vextracti128_s(inst),
            //   Mnemonic::Vmovd => self.vmovd_s(inst),
            //   Mnemonic::Vmovdqa => self.vmovdqa_s(inst),
            //   Mnemonic::Vmovdqu => self.vmovdqu_s(inst),
            //   Mnemonic::Vmovntdq => self.vmovntdq_s(inst),
            //   Mnemonic::Vmovq => self.vmovq_s(inst),
            //   Mnemonic::Vmovsd => self.vmovsd_s(inst),
            //   Mnemonic::Vmovaps => self.vmovaps_s(inst),
            //   Mnemonic::Vmovups => self.vmovups_s(inst),
            //   Mnemonic::Vpackuswb => self.vpackuswb_s(inst),
            //   Mnemonic::Vpackssdw => self.vpackssdw_s(inst),
            //   Mnemonic::Vpacksswb => self.vpacksswb_s(inst),
            //   Mnemonic::Vpaddb => self.vpaddb_s(inst),
            //   Mnemonic::Vpaddd => self.vpaddd_s(inst),
            //   Mnemonic::Vpaddw => self.vpaddw_s(inst),
            //   Mnemonic::Vpand => self.vpand_s(inst),
            //   Mnemonic::Vpandn => self.vpandn_s(inst),
            //   Mnemonic::Vperm2i128 => self.vperm2i128_s(inst),
            //   Mnemonic::Vpermq => self.vpermq_s(inst),
            //   Mnemonic::Vpextrb => self.vpextrb_s(inst),
            //   Mnemonic::Vpextrd => self.vpextrd_s(inst),
            //   Mnemonic::Vpextrq => self.vpextrq_s(inst),
            //   Mnemonic::Vpextrw => self.vpextrw_s(inst),
            //   Mnemonic::Vpbroadcastb => self.vpbroadcastb_s(inst),
            //   Mnemonic::Vpcmpeqb => self.vpcmpeqb_s(inst),
            //   Mnemonic::Vpcmpeqd => self.vpcmpeqd_s(inst),
            //   Mnemonic::Vpcmpeqq => self.vpcmpeqq_s(inst),
            //   Mnemonic::Vpcmpeqw => self.vpcmpeqw_s(inst),
            //   Mnemonic::Vpcmpgtb => self.vpcmpgtb_s(inst),
            //   Mnemonic::Vpcmpgtd => self.vpcmpgtd_s(inst),
            //   Mnemonic::Vpcmpgtw => self.vpcmpgtw_s(inst),
            //   Mnemonic::Vpmaddwd => self.vpmaddwd_s(inst),
            //   Mnemonic::Vpmovmskb => self.vpmovmskb_s(inst),
            //   Mnemonic::Vpminub => self.vpminub_s(inst),
            //   Mnemonic::Vpmulhw => self.vpmulhw_s(inst),
            //   Mnemonic::Vpmullw => self.vpmullw_s(inst),
            //   Mnemonic::Vpor => self.vpor_s(inst),
            //   Mnemonic::Vpshufd => self.vpshufd_s(inst),
            //   Mnemonic::Vpsignw => self.vpsignw_s(inst),
            //   Mnemonic::Vpslldq => self.vpslldq_s(inst),
            //   Mnemonic::Vpsllw => self.vpsllw_s(inst),
            //   Mnemonic::Vpsrad => self.vpsrad_s(inst),
            //   Mnemonic::Vpsraw => self.vpsraw_s(inst),
            //   Mnemonic::Vpsrldq => self.vpsrldq_s(inst),
            //   Mnemonic::Vpsrlw => self.vpsrlw_s(inst),
            //   Mnemonic::Vpsubb => self.vpsubb_s(inst),
            //   Mnemonic::Vpsubd => self.vpsubd_s(inst),
            //   Mnemonic::Vpsubq => self.vpsubq_s(inst),
            //   Mnemonic::Vpsubw => self.vpsubw_s(inst),
            //   Mnemonic::Vptest => self.vptest_s(inst),
            //   Mnemonic::Vpunpckhbw => self.vpunpckhbw_s(inst),
            //   Mnemonic::Vpunpckhdq => self.vpunpckhdq_s(inst),
            //   Mnemonic::Vpunpckhqdq => self.vpunpckhqdq_s(inst),
            //   Mnemonic::Vpunpckhwd => self.vpunpckhwd_s(inst),
            //   Mnemonic::Vpunpcklbw => self.vpunpcklbw_s(inst),
            //   Mnemonic::Vpunpckldq => self.vpunpckldq_s(inst),
            //   Mnemonic::Vpunpcklqdq => self.vpunpcklqdq_s(inst),
            //   Mnemonic::Vpunpcklwd => self.vpunpcklwd_s(inst),
            //   Mnemonic::Vpxor => self.vpxor_s(inst),
            //   Mnemonic::Vxorps => self.vxorps_s(inst),
            //   Mnemonic::Wait => self.wait_s(inst),
            //   Mnemonic::Wbinvd => self.wbinvd_s(inst),
            //   Mnemonic::Xadd => self.xadd_s(inst),
            //   Mnemonic::Xchg => self.xchg_s(inst),
            //   Mnemonic::Xor => self.xor_s(inst),
            //   Mnemonic::Xorpd => self.xorpd_s(inst),
            //   Mnemonic::Xorps => self.xorps_s(inst),
            // _ => return false,
            m => todo!("{:?}", m),
            //   default:
            // self.exception = triton::arch::FAULT_UD;
            //     break;
        }
        return true;
    }

    //       fn alignAddStack_s(&mut self, inst: x86Instruction, delta: u32) -> u64 {
    //         let dst = Operand::Register(self.architecture.get_stack_pointer());

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.bv(delta, dst.get_bit_size());

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvadd(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "Stack alignment");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Return the new stack value */
    //         return node.evaluate() as u64;
    //       }

    //       fn alignSubStack_s(&mut self, inst: x86Instruction, delta: u32) -> u64 {
    //         let dst = Operand::Register(self.architecture.get_stack_pointer());

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.bv(delta, dst.get_bit_size());

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvsub(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "Stack alignment");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Return the new stack value */
    //         return node.evaluate() as u64;
    //       }

    //       fn clearFlag_s(&mut self, inst: x86Instruction, flag: Register, comment: &str) {
    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bv(0, 1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, flag, comment);

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(flag, triton::engines::taint::UNTAINTED);
    //       }

    //       fn setFlag_s(&mut self, inst: x86Instruction, flag: Register, comment: &str) {
    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bv(1, 1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, flag, comment);

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(flag, triton::engines::taint::UNTAINTED);
    //       }

    //       fn undefined_s(&mut self, inst: x86Instruction, reg: Register) {
    //         // if (self.modes.isModeEnabled(triton::modes::CONCRETIZE_UNDEFINED_REGISTERS)) {
    //         //   self.symbolicEngine.concretizeRegister(reg);
    //         // }
    //         /* Tell that the instruction defines a register as undefined and untaint */
    //         inst.setUndefinedRegister(reg);
    //         // self.taintEngine.setTaintRegister(reg, triton::engines::taint::UNTAINTED);
    //       }

    //       fn controlFlow_s(&mut self, inst: x86Instruction) {
    //         let pc      = Operand::Register(self.architecture.get_program_counter());
    //         let counter = Operand::Register(Register::CX.full_register());
    //         let zf      = Operand::Register(Register::ZF);

    //         match (inst.prefix) {

    //           triton::arch::x86::ID_PREFIX_REP => {
    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, counter);

    //             /* Create the semantics for Counter */
    //             let node1 = self.ast_ctxt.ite(
    //                            self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, counter.get_bit_size())),
    //                            op1,
    //                            self.ast_ctxt.bvsub(op1, self.ast_ctxt.bv(1, counter.get_bit_size()))
    //                          );

    //             /* Create the semantics for PC */
    //             let node2 = self.ast_ctxt.ite(
    //                            self.ast_ctxt.equal(node1, self.ast_ctxt.bv(0, counter.get_bit_size())),
    //                            self.ast_ctxt.bv(inst.next_ip(), pc.get_bit_size()),
    //                            self.ast_ctxt.bv(inst.ip(), pc.get_bit_size())
    //                          );

    //             /* Create symbolic expression */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, counter, "Counter operation");
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, pc, "Program Counter");

    //             /* Spread taint for PC */
    //             // expr1.isTainted = self.taintEngine.taintUnion(counter, counter);
    //             // expr2.isTainted = self.taintEngine.taintAssignment(pc, counter);
    //           }

    //           triton::arch::x86::ID_PREFIX_REPE => {
    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, counter);
    //             let op2 = self.symbolicEngine.getOperandAst(inst, zf);

    //             /* Create the semantics for Counter */
    //             let node1 = self.ast_ctxt.ite(
    //                            self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, counter.get_bit_size())),
    //                            op1,
    //                            self.ast_ctxt.bvsub(op1, self.ast_ctxt.bv(1, counter.get_bit_size()))
    //                          );

    //             /* Create the semantics for PC */
    //             let node2 = self.ast_ctxt.ite(
    //                            self.ast_ctxt.lor(
    //                              self.ast_ctxt.equal(node1, self.ast_ctxt.bv(0, counter.get_bit_size())),
    //                              self.ast_ctxt.equal(op2, self.ast_ctxt.bvfalse())
    //                            ),
    //                            self.ast_ctxt.bv(inst.next_ip(), pc.get_bit_size()),
    //                            self.ast_ctxt.bv(inst.ip(), pc.get_bit_size())
    //                          );

    //             /* Create symbolic expression */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, counter, "Counter operation");
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, pc, "Program Counter");

    //             /* Spread taint */
    //             // expr1.isTainted = self.taintEngine.taintUnion(counter, counter);
    //             // expr2.isTainted = self.taintEngine.taintAssignment(pc, counter);
    //           }

    //           triton::arch::x86::ID_PREFIX_REPNE => {
    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, counter);
    //             let op2 = self.symbolicEngine.getOperandAst(inst, zf);

    //             /* Create the semantics for Counter */
    //             let node1 = self.ast_ctxt.ite(
    //                            Operand::Instruction(self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, counter.get_bit_size()))),
    //                            op1,
    //                            Operand::Instruction(self.ast_ctxt.bvsub(op1, self.ast_ctxt.bv(1, counter.get_bit_size())))
    //                          );

    //             /* Create the semantics for PC */
    //             let node2 = self.ast_ctxt.ite(
    //                            Operand::Instruction(self.ast_ctxt.lor(
    //                              self.ast_ctxt.equal(node1, self.ast_ctxt.bv(0, counter.get_bit_size())),
    //                              self.ast_ctxt.equal(op2, self.ast_ctxt.bvtrue())
    //                            )),
    //                            Operand::Instruction(self.ast_ctxt.bv(inst.next_ip(), pc.get_bit_size())),
    //                            Operand::Instruction(self.ast_ctxt.bv(inst.ip(), pc.get_bit_size()))
    //                          );

    //             /* Create symbolic expression */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, counter, "Counter operation");
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, pc, "Program Counter");

    //             /* Spread taint */
    //             // expr1.isTainted = self.taintEngine.taintUnion(counter, counter);
    //             // expr2.isTainted = self.taintEngine.taintAssignment(pc, counter);
    //           }

    //           _ => {
    //             /* Create the semantics */
    //             let node = self.ast_ctxt.bv(inst.next_ip(), pc.get_bit_size());

    //             /* Create symbolic expression */
    //             let expr = self.symbolicEngine.createSymbolicRegisterExpression(inst, node, self.architecture.get_program_counter(), "Program Counter");

    //             /* Spread taint */
    //             // expr.isTainted = self.taintEngine.setTaintRegister(self.architecture.get_program_counter(), triton::engines::taint::UNTAINTED);
    //           }
    //         }
    //       }

    //       /// Update the FPU x87 Tag Word (whenever an STX register changes)
    //       fn updateFTW(&mut self, inst: x86Instruction, parent: InstructionIdx) {
    //         /* Fetch the STX registers */
    //         let st0 = Operand::Register(Register::ST0);
    //         let st1 = Operand::Register(Register::ST1);
    //         let st2 = Operand::Register(Register::ST2);
    //         let st3 = Operand::Register(Register::ST3);
    //         let st4 = Operand::Register(Register::ST4);
    //         let st5 = Operand::Register(Register::ST5);
    //         let st6 = Operand::Register(Register::ST6);
    //         let st7 = Operand::Register(Register::ST7);

    //         /* Fetch the STX ASTs */
    //         let st0_ast = self.symbolicEngine.getOperandAst(inst, st0);
    //         let st1_ast = self.symbolicEngine.getOperandAst(inst, st1);
    //         let st2_ast = self.symbolicEngine.getOperandAst(inst, st2);
    //         let st3_ast = self.symbolicEngine.getOperandAst(inst, st3);
    //         let st4_ast = self.symbolicEngine.getOperandAst(inst, st4);
    //         let st5_ast = self.symbolicEngine.getOperandAst(inst, st5);
    //         let st6_ast = self.symbolicEngine.getOperandAst(inst, st6);
    //         let st7_ast = self.symbolicEngine.getOperandAst(inst, st7);

    //         /* Extract the fraction from the STX registers */
    //         let fraction_st0 = Operand::Instruction(self.ast_ctxt.extract(62, 0, st0_ast));
    //         let fraction_st1 = Operand::Instruction(self.ast_ctxt.extract(62, 0, st1_ast));
    //         let fraction_st2 = Operand::Instruction(self.ast_ctxt.extract(62, 0, st2_ast));
    //         let fraction_st3 = Operand::Instruction(self.ast_ctxt.extract(62, 0, st3_ast));
    //         let fraction_st4 = Operand::Instruction(self.ast_ctxt.extract(62, 0, st4_ast));
    //         let fraction_st5 = Operand::Instruction(self.ast_ctxt.extract(62, 0, st5_ast));
    //         let fraction_st6 = Operand::Instruction(self.ast_ctxt.extract(62, 0, st6_ast));
    //         let fraction_st7 = Operand::Instruction(self.ast_ctxt.extract(62, 0, st7_ast));

    //         /* Extract the integer bit from the STX registers */
    //         let integer_st0 = Operand::Instruction(self.ast_ctxt.extract(63, 63, st0_ast));
    //         let integer_st1 = Operand::Instruction(self.ast_ctxt.extract(63, 63, st1_ast));
    //         let integer_st2 = Operand::Instruction(self.ast_ctxt.extract(63, 63, st2_ast));
    //         let integer_st3 = Operand::Instruction(self.ast_ctxt.extract(63, 63, st3_ast));
    //         let integer_st4 = Operand::Instruction(self.ast_ctxt.extract(63, 63, st4_ast));
    //         let integer_st5 = Operand::Instruction(self.ast_ctxt.extract(63, 63, st5_ast));
    //         let integer_st6 = Operand::Instruction(self.ast_ctxt.extract(63, 63, st6_ast));
    //         let integer_st7 = Operand::Instruction(self.ast_ctxt.extract(63, 63, st7_ast));

    //         /* Extract the exponent from the STX registers */
    //         let exponent_st0 = Operand::Instruction(self.ast_ctxt.extract(79, 64, st0_ast));
    //         let exponent_st1 = Operand::Instruction(self.ast_ctxt.extract(79, 64, st1_ast));
    //         let exponent_st2 = Operand::Instruction(self.ast_ctxt.extract(79, 64, st2_ast));
    //         let exponent_st3 = Operand::Instruction(self.ast_ctxt.extract(79, 64, st3_ast));
    //         let exponent_st4 = Operand::Instruction(self.ast_ctxt.extract(79, 64, st4_ast));
    //         let exponent_st5 = Operand::Instruction(self.ast_ctxt.extract(79, 64, st5_ast));
    //         let exponent_st6 = Operand::Instruction(self.ast_ctxt.extract(79, 64, st6_ast));
    //         let exponent_st7 = Operand::Instruction(self.ast_ctxt.extract(79, 64, st7_ast));

    //         /* Exponent All Zeros */
    //         let ea0_st0 = self.ast_ctxt.equal(exponent_st0, Operand::Instruction(self.ast_ctxt.bv(0x0000, 16)));
    //         let ea0_st1 = self.ast_ctxt.equal(exponent_st1, Operand::Instruction(self.ast_ctxt.bv(0x0000, 16)));
    //         let ea0_st2 = self.ast_ctxt.equal(exponent_st2, Operand::Instruction(self.ast_ctxt.bv(0x0000, 16)));
    //         let ea0_st3 = self.ast_ctxt.equal(exponent_st3, Operand::Instruction(self.ast_ctxt.bv(0x0000, 16)));
    //         let ea0_st4 = self.ast_ctxt.equal(exponent_st4, Operand::Instruction(self.ast_ctxt.bv(0x0000, 16)));
    //         let ea0_st5 = self.ast_ctxt.equal(exponent_st5, Operand::Instruction(self.ast_ctxt.bv(0x0000, 16)));
    //         let ea0_st6 = self.ast_ctxt.equal(exponent_st6, Operand::Instruction(self.ast_ctxt.bv(0x0000, 16)));
    //         let ea0_st7 = self.ast_ctxt.equal(exponent_st7, Operand::Instruction(self.ast_ctxt.bv(0x0000, 16)));

    //         /* Exponent All Ones */
    //         let ea1_st0 = self.ast_ctxt.equal(exponent_st0, Operand::Instruction(self.ast_ctxt.bv(0xFFFF, 16)));
    //         let ea1_st1 = self.ast_ctxt.equal(exponent_st1, Operand::Instruction(self.ast_ctxt.bv(0xFFFF, 16)));
    //         let ea1_st2 = self.ast_ctxt.equal(exponent_st2, Operand::Instruction(self.ast_ctxt.bv(0xFFFF, 16)));
    //         let ea1_st3 = self.ast_ctxt.equal(exponent_st3, Operand::Instruction(self.ast_ctxt.bv(0xFFFF, 16)));
    //         let ea1_st4 = self.ast_ctxt.equal(exponent_st4, Operand::Instruction(self.ast_ctxt.bv(0xFFFF, 16)));
    //         let ea1_st5 = self.ast_ctxt.equal(exponent_st5, Operand::Instruction(self.ast_ctxt.bv(0xFFFF, 16)));
    //         let ea1_st6 = self.ast_ctxt.equal(exponent_st6, Operand::Instruction(self.ast_ctxt.bv(0xFFFF, 16)));
    //         let ea1_st7 = self.ast_ctxt.equal(exponent_st7, Operand::Instruction(self.ast_ctxt.bv(0xFFFF, 16)));

    //         /* Exponent Neither All Zeroes Or Ones */
    //         let ena01_st0 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st0, ea1_st0), self.ast_ctxt.bvfalse());
    //         let ena01_st1 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st1, ea1_st1), self.ast_ctxt.bvfalse());
    //         let ena01_st2 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st2, ea1_st2), self.ast_ctxt.bvfalse());
    //         let ena01_st3 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st3, ea1_st3), self.ast_ctxt.bvfalse());
    //         let ena01_st4 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st4, ea1_st4), self.ast_ctxt.bvfalse());
    //         let ena01_st5 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st5, ea1_st5), self.ast_ctxt.bvfalse());
    //         let ena01_st6 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st6, ea1_st6), self.ast_ctxt.bvfalse());
    //         let ena01_st7 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st7, ea1_st7), self.ast_ctxt.bvfalse());

    //         /* Integer Bit 0 */
    //         let ib0_st0 = self.ast_ctxt.equal(integer_st0, self.ast_ctxt.bv(0, 1));
    //         let ib0_st1 = self.ast_ctxt.equal(integer_st1, self.ast_ctxt.bv(0, 1));
    //         let ib0_st2 = self.ast_ctxt.equal(integer_st2, self.ast_ctxt.bv(0, 1));
    //         let ib0_st3 = self.ast_ctxt.equal(integer_st3, self.ast_ctxt.bv(0, 1));
    //         let ib0_st4 = self.ast_ctxt.equal(integer_st4, self.ast_ctxt.bv(0, 1));
    //         let ib0_st5 = self.ast_ctxt.equal(integer_st5, self.ast_ctxt.bv(0, 1));
    //         let ib0_st6 = self.ast_ctxt.equal(integer_st6, self.ast_ctxt.bv(0, 1));
    //         let ib0_st7 = self.ast_ctxt.equal(integer_st7, self.ast_ctxt.bv(0, 1));

    //         /* Fraction All Zeroes */
    //         let fa0_st0 = self.ast_ctxt.equal(fraction_st0, self.ast_ctxt.bv(0, 63));
    //         let fa0_st1 = self.ast_ctxt.equal(fraction_st1, self.ast_ctxt.bv(0, 63));
    //         let fa0_st2 = self.ast_ctxt.equal(fraction_st2, self.ast_ctxt.bv(0, 63));
    //         let fa0_st3 = self.ast_ctxt.equal(fraction_st3, self.ast_ctxt.bv(0, 63));
    //         let fa0_st4 = self.ast_ctxt.equal(fraction_st4, self.ast_ctxt.bv(0, 63));
    //         let fa0_st5 = self.ast_ctxt.equal(fraction_st5, self.ast_ctxt.bv(0, 63));
    //         let fa0_st6 = self.ast_ctxt.equal(fraction_st6, self.ast_ctxt.bv(0, 63));
    //         let fa0_st7 = self.ast_ctxt.equal(fraction_st7, self.ast_ctxt.bv(0, 63));

    //         /* Determine the x87 FPU Tag Word (Diagram at page 379 of the AMD Architecture Programmer's Manual, Volume 2: System Programming) */
    //         let db_1_0 = self.ast_ctxt.ite(ea0_st0,
    //             self.ast_ctxt.ite(ib0_st0,
    //               self.ast_ctxt.ite(fa0_st0,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st0,
    //               self.ast_ctxt.ite(ib0_st0,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2)));    // 'Exponent All 1'

    //         let db_3_2 = self.ast_ctxt.ite(ea0_st1,
    //             self.ast_ctxt.ite(ib0_st1,
    //               self.ast_ctxt.ite(fa0_st1,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st1,
    //               self.ast_ctxt.ite(ib0_st1,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2)));    // 'Exponent All 1'

    //         let db_5_4 = self.ast_ctxt.ite(ea0_st2,
    //             self.ast_ctxt.ite(ib0_st2,
    //               self.ast_ctxt.ite(fa0_st2,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st2,
    //               self.ast_ctxt.ite(ib0_st2,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2)));    // 'Exponent All 1'

    //         let db_7_6 = self.ast_ctxt.ite(ea0_st3,
    //             self.ast_ctxt.ite(ib0_st3,
    //               self.ast_ctxt.ite(fa0_st3,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st3,
    //               self.ast_ctxt.ite(ib0_st3,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2)));    // 'Exponent All 1'

    //         let db_9_8 = self.ast_ctxt.ite(ea0_st4,
    //             self.ast_ctxt.ite(ib0_st4,
    //               self.ast_ctxt.ite(fa0_st4,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st4,
    //               self.ast_ctxt.ite(ib0_st4,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2)));    // 'Exponent All 1'

    //         let db_11_10 = self.ast_ctxt.ite(ea0_st5,
    //             self.ast_ctxt.ite(ib0_st5,
    //               self.ast_ctxt.ite(fa0_st5,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st5,
    //               self.ast_ctxt.ite(ib0_st5,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2)));    // 'Exponent All 1'

    //         let db_13_12 = self.ast_ctxt.ite(ea0_st6,
    //             self.ast_ctxt.ite(ib0_st6,
    //               self.ast_ctxt.ite(fa0_st6,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st6,
    //               self.ast_ctxt.ite(ib0_st6,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2)));    // 'Exponent All 1'

    //         let db_15_14 = self.ast_ctxt.ite(ea0_st7,
    //             self.ast_ctxt.ite(ib0_st7,
    //               self.ast_ctxt.ite(fa0_st7,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st7,
    //               self.ast_ctxt.ite(ib0_st7,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2)));    // 'Exponent All 1'

    //         /* Restore the x87 FPU Tag Word */
    //         let node = self.ast_ctxt.concat(db_15_14,
    //           self.ast_ctxt.concat(db_13_12,
    //           self.ast_ctxt.concat(db_11_10,
    //           self.ast_ctxt.concat(db_9_8,
    //           self.ast_ctxt.concat(db_7_6,
    //           self.ast_ctxt.concat(db_5_4,
    //           self.ast_ctxt.concat(db_3_2, db_1_0)))))));

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::FTW, "x87 FPU Tag Word");

    //         /* Spread the taint from the parent to the child */
    //         // let st0_taint = self.taintEngine.isRegisterTainted(Register::ST0);
    //         // let st1_taint = self.taintEngine.isRegisterTainted(Register::ST1);
    //         // let st2_taint = self.taintEngine.isRegisterTainted(Register::ST2);
    //         // let st3_taint = self.taintEngine.isRegisterTainted(Register::ST3);
    //         // let st4_taint = self.taintEngine.isRegisterTainted(Register::ST4);
    //         // let st5_taint = self.taintEngine.isRegisterTainted(Register::ST5);
    //         // let st6_taint = self.taintEngine.isRegisterTainted(Register::ST6);
    //         // let st7_taint = self.taintEngine.isRegisterTainted(Register::ST7);

    //         // let is_ftw_tainted = st0_taint | st1_taint | st2_taint | st3_taint |
    //         //                       st4_taint | st5_taint | st6_taint | st7_taint;

    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::FTW, is_ftw_tainted);
    //       }

    fn af_s(
        &mut self,
        inst: x86Instruction,
        parent: InstructionIdx,
        dst: OperandWrapper,
        op1: Operand,
        op2: Operand,
    ) {
        // todo: optional arg
        let vol: bool = false;

        let bvSize = dst.get_bit_size();
        let low = if vol { 0 } else { dst.get_low() };
        let high = if vol { bvSize - 1 } else { dst.get_high() };

        /*
         * Create the semantic.
         * af = 0x10 == (0x10 & (regDst ^ op1 ^ op2))
         */
        let node = self.ast_ctxt.ite(
            Operand::Instruction(self.ast_ctxt.equal(
                Operand::Instruction(self.ast_ctxt.bv(0x10, bvSize)),
                Operand::Instruction(self.ast_ctxt.bvand(
                    Operand::Instruction(self.ast_ctxt.bv(0x10, bvSize)),
                    Operand::Instruction(self.ast_ctxt.bvxor(
                        Operand::Instruction(self.ast_ctxt.extract(
                            high,
                            low,
                            Operand::Instruction(parent),
                        )),
                        Operand::Instruction(self.ast_ctxt.bvxor(op1, op2)),
                    )),
                )),
            )),
            Operand::Instruction(self.ast_ctxt.bv(1, 1)),
            Operand::Instruction(self.ast_ctxt.bv(0, 1)),
        );

        /* Create the symbolic expression */
        // let expr =
        //     self.symbolicEngine
        //         .createSymbolicExpression(inst, node, Register::AF, "Adjust flag");

        /* Spread the taint from the parent to the child */
        // expr.isTainted = self.taintEngine.setTaintRegister(Register::AF, parent.isTainted);
    }

    //       fn afAaa_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op3: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();

    //         /*
    //          * Create the semantic.
    //          * af = 1 if ((AL AND 0FH) > 9) or (AF = 1) then 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.lor(
    //                         self.ast_ctxt.bvugt(
    //                           self.ast_ctxt.bvand(op1, self.ast_ctxt.bv(0xf, bvSize)),
    //                           self.ast_ctxt.bv(9, bvSize)
    //                         ),
    //                         self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue())
    //                       ),
    //                       self.ast_ctxt.bv(1, 1),
    //                       self.ast_ctxt.bv(0, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::AF, "Adjust flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::AF, parent.isTainted);
    //       }

    //       fn afNeg_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let low = if vol { 0 } else { dst.get_low() };
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};

    //         /*
    //          * Create the semantic.
    //          * af = 0x10 == (0x10 & (op1 ^ regDst))
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.bv(0x10, bvSize),
    //                         self.ast_ctxt.bvand(
    //                           self.ast_ctxt.bv(0x10, bvSize),
    //                           self.ast_ctxt.bvxor(
    //                             op1,
    //                             self.ast_ctxt.extract(high, low, Operand::Instruction(parent))
    //                           )
    //                         )
    //                       ),
    //                       self.ast_ctxt.bv(1, 1),
    //                       self.ast_ctxt.bv(0, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::AF, "Adjust flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::AF, parent.isTainted);
    //       }

    //       fn cfAaa_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op3: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();

    //         /*
    //          * Create the semantic.
    //          * cf = 1 if ((AL AND 0FH) > 9) or (AF = 1) then 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.lor(
    //                         self.ast_ctxt.bvugt(
    //                           self.ast_ctxt.bvand(op1, self.ast_ctxt.bv(0xf, bvSize)),
    //                           self.ast_ctxt.bv(9, bvSize)
    //                         ),
    //                         self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue())
    //                       ),
    //                       self.ast_ctxt.bv(1, 1),
    //                       self.ast_ctxt.bv(0, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfAdd_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let low = if vol { 0 } else { dst.get_low() };
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};

    //         /*
    //          * Create the semantic.
    //          * cf = MSB((op1 & op2) ^ ((op1 ^ op2 ^ parent) & (op1 ^ op2)));
    //          */
    //         let node = self.ast_ctxt.extract(bvSize-1, bvSize-1,
    //                       self.ast_ctxt.bvxor(
    //                         self.ast_ctxt.bvand(op1, op2),
    //                         self.ast_ctxt.bvand(
    //                           self.ast_ctxt.bvxor(
    //                             self.ast_ctxt.bvxor(op1, op2),
    //                             self.ast_ctxt.extract(high, low, Operand::Instruction(parent))
    //                           ),
    //                         self.ast_ctxt.bvxor(op1, op2))
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfBlsi_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         /*
    //          * Create the semantic.
    //          * cf = 0 if op1 == 0 else 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         op1,
    //                         self.ast_ctxt.bv(0, dst.get_bit_size())
    //                       ),
    //                       self.ast_ctxt.bv(0, 1),
    //                       self.ast_ctxt.bv(1, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfBlsmsk_s(&mut self, inst: x86Instruction,
    //                                     parent: InstructionIdx,
    //                                     dst: OperandWrapper,
    //                                     op1: Operand,
    //                                     ) {
    //                                         // todo: optional arg
    //                                         let vol: bool = false;

    //         /*
    //          * Create the semantic.
    //          * cf = 1 if op1 == 0 else 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         op1,
    //                         self.ast_ctxt.bv(0, dst.get_bit_size())
    //                       ),
    //                       self.ast_ctxt.bv(1, 1),
    //                       self.ast_ctxt.bv(0, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfBlsr_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         /*
    //          * Create the semantic.
    //          * cf = 1 if op1 == 0 else 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         op1,
    //                         self.ast_ctxt.bv(0, dst.get_bit_size())
    //                       ),
    //                       self.ast_ctxt.bv(1, 1),
    //                       self.ast_ctxt.bv(0, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfImul_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   res: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         /*
    //          * Create the semantic.
    //          * cf = 0 if sx(dst) == node else 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.sx(dst.get_bit_size(), op1),
    //                         res
    //                       ),
    //                       self.ast_ctxt.bv(0, 1),
    //                       self.ast_ctxt.bv(1, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfLzcnt_s(&mut self, inst: x86Instruction,
    //                                    parent: InstructionIdx,
    //                                    src: OperandWrapper,
    //                                    op1: Operand,
    //                                    ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = src.get_bit_size();
    //         let low    = if vol { 0 } else {src.get_low()};
    //         let high   = if vol  {bvSize-1 } else {src.get_high()};

    //         /*
    //          * Create the semantic.
    //          * cf = 0 == parent
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.extract(high, low, op1),
    //                         self.ast_ctxt.bv(0, bvSize)
    //                       ),
    //                       self.ast_ctxt.bv(1, 1),
    //                       self.ast_ctxt.bv(0, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfMul_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         /*
    //          * Create the semantic.
    //          * cf = 0 if op1 == 0 else 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         op1,
    //                         self.ast_ctxt.bv(0, dst.get_bit_size())
    //                       ),
    //                       self.ast_ctxt.bv(0, 1),
    //                       self.ast_ctxt.bv(1, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfNeg_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         /*
    //          * Create the semantic.
    //          * cf = 0 if op1 == 0 else 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         op1,
    //                         self.ast_ctxt.bv(0, dst.get_bit_size())
    //                       ),
    //                       self.ast_ctxt.bv(0, 1),
    //                       self.ast_ctxt.bv(1, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfPtest_s(&mut self, inst: x86Instruction,
    //                                    parent: InstructionIdx,
    //                                    dst: OperandWrapper,
    //                                    ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let low = if vol { 0 } else { dst.get_low() };
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};

    //         /*
    //          * Create the semantic.
    //          * cf = 0 == regDst
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.extract(high, low, Operand::Instruction(parent)),
    //                         self.ast_ctxt.bv(0, bvSize)
    //                       ),
    //                       self.ast_ctxt.bv(1, 1),
    //                       self.ast_ctxt.bv(0, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn cfRcl_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  result: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = op2.getBitvectorSize();
    //         let high   = result.getBitvectorSize() - 1;
    //         let cf     = Operand::Register(Register::CF);

    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.extract(high, high, result)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         // if (op2.evaluate()) {
    //         //   /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         // }
    //         // else {
    //         //   inst.removeWrittenRegister(cf.getConstRegister());
    //         // }
    //       }

    //       fn cfRcr_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  result: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = op2.getBitvectorSize();
    //         let high   = result.getBitvectorSize() - 1;
    //         let cf     = Operand::Register(Register::CF);

    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.extract(high, high, result) /* yes it's should be LSB, but here it's a trick :-) */
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         // if (op2.evaluate()) {
    //         //   /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         // }
    //         // else {
    //         //   inst.removeWrittenRegister(cf.getConstRegister());
    //         // }
    //       }

    //       fn cfRol_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = op2.getBitvectorSize();
    //         let low = if vol { 0 } else { dst.get_low() };
    //         let cf     = Operand::Register(Register::CF);

    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.extract(low, low, Operand::Instruction(parent))
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(cf.getConstRegister());
    //         }
    //       }

    //       fn cfRor_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = op2.getBitvectorSize();
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};
    //         let cf     = Operand::Register(Register::CF);

    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.extract(high, high, Operand::Instruction(parent))
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(cf.getConstRegister());
    //         }
    //       }

    //       fn cfSar_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let cf     = Operand::Register(Register::CF);

    //         /*
    //          * Create the semantic.
    //          * if op2 != 0:
    //          *   if op2 > bvSize:
    //          *     cf.id = ((op1 >> (bvSize - 1)) & 1)
    //          *   else:
    //          *     cf.id = ((op1 >> (op2 - 1)) & 1)
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.ite(
    //                         self.ast_ctxt.bvugt(op2, self.ast_ctxt.bv(bvSize, bvSize)),
    //                         self.ast_ctxt.extract(0, 0, self.ast_ctxt.bvlshr(op1, self.ast_ctxt.bvsub(self.ast_ctxt.bv(bvSize, bvSize), self.ast_ctxt.bv(1, bvSize)))),
    //                         self.ast_ctxt.extract(0, 0, self.ast_ctxt.bvlshr(op1, self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(1, bvSize))))
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(cf.getConstRegister());
    //         }
    //       }

    //       fn cfShl_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let cf     = Operand::Register(Register::CF);

    //         /*
    //          * Create the semantic.
    //          * cf = (op1 >> ((bvSize - op2) & 1) if op2 != 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.extract(0, 0,
    //                         self.ast_ctxt.bvlshr(
    //                           op1,
    //                           self.ast_ctxt.bvsub(
    //                             self.ast_ctxt.bv(bvSize, bvSize),
    //                             op2
    //                           )
    //                         )
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(cf.getConstRegister());
    //         }
    //       }

    //       fn cfShld_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   op2: Operand,
    //                                   op3: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bv1Size = op1.getBitvectorSize();
    //         let bv2Size = op2.getBitvectorSize();
    //         let bv3Size = op3.getBitvectorSize();
    //         let cf      = Operand::Register(Register::CF);

    //         /*
    //          * Create the semantic.
    //          * cf = MSB(rol(op3, concat(op2,op1))) if op3 != 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op3, self.ast_ctxt.bv(0, bv3Size)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.extract(
    //                         dst.get_bit_size(), dst.get_bit_size(),
    //                         self.ast_ctxt.bvrol(
    //                           self.ast_ctxt.concat(op2, op1),
    //                           self.ast_ctxt.zx(((bv1Size + bv2Size) - bv3Size), op3)
    //                         )
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         if (op3.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(cf.getConstRegister());
    //         }
    //       }

    //       fn cfShr_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let cf     = Operand::Register(Register::CF);

    //         /*
    //          * Create the semantic.
    //          * cf = ((op1 >> (op2 - 1)) & 1) if op2 != 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.extract(0, 0,
    //                         self.ast_ctxt.bvlshr(
    //                           op1,
    //                           self.ast_ctxt.bvsub(
    //                             op2,
    //                             self.ast_ctxt.bv(1, bvSize))
    //                         )
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(cf.getConstRegister());
    //         }
    //       }

    //       fn cfShrd_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   op2: Operand,
    //                                   op3: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize  = dst.get_bit_size();
    //         let bv1Size = op1.getBitvectorSize();
    //         let bv2Size = op2.getBitvectorSize();
    //         let bv3Size = op3.getBitvectorSize();
    //         let cf      = Operand::Register(Register::CF);

    //         /*
    //          * Create the semantic.
    //          * cf = MSB(ror(op3, concat(op2,op1))) if op3 != 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op3, self.ast_ctxt.bv(0, bv3Size)),
    //                       self.symbolicEngine.getOperandAst(cf),
    //                       self.ast_ctxt.extract(
    //                         (bvSize * 2) - 1, (bvSize * 2) - 1,
    //                         self.ast_ctxt.bvror(
    //                           self.ast_ctxt.concat(op2, op1),
    //                           self.ast_ctxt.zx(((bv1Size + bv2Size) - bv3Size), op3)
    //                         )
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, cf.getConstRegister(), "Carry flag");

    //         if (op3.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(cf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(cf.getConstRegister());
    //         }
    //       }

    fn cfSub_s(
        &mut self,
        inst: x86Instruction,
        parent: InstructionIdx,
        dst: OperandWrapper,
        op1: Operand,
        op2: Operand,
    ) {
        // todo: optional arg
        let vol: bool = false;

        let bvSize = dst.get_bit_size();
        let low = if vol { 0 } else { dst.get_low() };
        let high = if vol { bvSize - 1 } else { dst.get_high() };

        /*
         * Create the semantic.
         * cf = extract(bvSize, bvSize (((op1 ^ op2 ^ res) ^ ((op1 ^ res) & (op1 ^ op2)))))
         */
        let node = self.ast_ctxt.extract(
            bvSize - 1,
            bvSize - 1,
            Operand::Instruction(self.ast_ctxt.bvxor(
                Operand::Instruction(self.ast_ctxt.bvxor(
                    op1,
                    Operand::Instruction(self.ast_ctxt.bvxor(
                        op2,
                        Operand::Instruction(self.ast_ctxt.extract(
                            high,
                            low,
                            Operand::Instruction(parent),
                        )),
                    )),
                )),
                Operand::Instruction(self.ast_ctxt.bvand(
                    Operand::Instruction(self.ast_ctxt.bvxor(
                        op1,
                        Operand::Instruction(self.ast_ctxt.extract(
                            high,
                            low,
                            Operand::Instruction(parent),
                        )),
                    )),
                    Operand::Instruction(self.ast_ctxt.bvxor(op1, op2)),
                )),
            )),
        );

        /* Create the symbolic expression */
        // let expr =
        //     self.symbolicEngine
        //         .createSymbolicExpression(inst, node, Register::CF, "Carry flag");

        /* Spread the taint from the parent to the child */
        // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    }

    //       fn cfTzcnt_s(&mut self, inst: x86Instruction,
    //                                    parent: InstructionIdx,
    //                                    src: OperandWrapper,
    //                                    op1: Operand,
    //                                    ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = src.get_bit_size();
    //         let low    = if vol { 0 } else {src.get_low()};
    //         let high   = if vol  {bvSize-1 } else {src.get_high()};

    //         /*
    //          * Create the semantic.
    //          * cf = 0 == parent
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.extract(high, low, op1),
    //                         self.ast_ctxt.bv(0, bvSize)
    //                       ),
    //                       self.ast_ctxt.bv(1, 1),
    //                       self.ast_ctxt.bv(0, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "Carry flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::CF, parent.isTainted);
    //       }

    //       fn ofAdd_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let low = if vol { 0 } else { dst.get_low() };
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};

    //         /*
    //          * Create the semantic.
    //          * of = MSB((op1 ^ ~op2) & (op1 ^ regDst))
    //          */
    //         let node = self.ast_ctxt.extract(bvSize-1, bvSize-1,
    //                       self.ast_ctxt.bvand(
    //                         self.ast_ctxt.bvxor(op1, self.ast_ctxt.bvnot(op2)),
    //                         self.ast_ctxt.bvxor(op1, self.ast_ctxt.extract(high, low, Operand::Instruction(parent)))
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::OF, "Overflow flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::OF, parent.isTainted);
    //       }

    //       fn ofImul_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   res: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;
    //         /*
    //          * Create the semantic.
    //          * of = 0 if sx(dst) == node else 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.sx(dst.get_bit_size(), op1),
    //                         res
    //                       ),
    //                       self.ast_ctxt.bv(0, 1),
    //                       self.ast_ctxt.bv(1, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::OF, "Overflow flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::OF, parent.isTainted);
    //       }

    //       fn ofMul_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         /*
    //          * Create the semantic.
    //          * of = 0 if up == 0 else 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         op1,
    //                         self.ast_ctxt.bv(0, dst.get_bit_size())
    //                       ),
    //                       self.ast_ctxt.bv(0, 1),
    //                       self.ast_ctxt.bv(1, 1)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::OF, "Overflow flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::OF, parent.isTainted);
    //       }

    //       fn ofNeg_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let low = if vol { 0 } else { dst.get_low() };
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};

    //         /*
    //          * Create the semantic.
    //          * of = (res & op1) >> (bvSize - 1) & 1
    //          */
    //         let node = self.ast_ctxt.extract(0, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         self.ast_ctxt.bvand(self.ast_ctxt.extract(high, low, Operand::Instruction(parent)), op1),
    //                         self.ast_ctxt.bvsub(self.ast_ctxt.bv(bvSize, bvSize), self.ast_ctxt.bv(1, bvSize))
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::OF, "Overflow flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::OF, parent.isTainted);
    //       }

    //       fn ofRol_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};
    //         let cf     = Operand::Register(Register::CF);
    //         let of     = Operand::Register(Register::OF);

    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(self.ast_ctxt.zx(bvSize - op2.getBitvectorSize(), op2), self.ast_ctxt.bv(1, bvSize)),
    //                       self.ast_ctxt.bvxor(
    //                         self.ast_ctxt.extract(high, high, Operand::Instruction(parent)),
    //                         self.symbolicEngine.getOperandAst(inst, cf)
    //                       ),
    //                       self.symbolicEngine.getOperandAst(of)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, of.getConstRegister(), "Overflow flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(of.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeReadRegister(cf.getConstRegister());
    //           inst.removeWrittenRegister(of.getConstRegister());
    //         }
    //       }

    //       fn ofRor_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = op2.getBitvectorSize();
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};
    //         let of     = Operand::Register(Register::OF);

    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(1, bvSize)),
    //                       self.ast_ctxt.bvxor(
    //                         self.ast_ctxt.extract(high, high, Operand::Instruction(parent)),
    //                         self.ast_ctxt.extract(high-1, high-1, Operand::Instruction(parent))
    //                       ),
    //                       self.symbolicEngine.getOperandAst(of)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, of.getConstRegister(), "Overflow flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(of.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(of.getConstRegister());
    //         }
    //       }

    //       fn ofRcr_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = op2.getBitvectorSize();
    //         let high   = dst.get_bit_size()-1;
    //         let cf     = Operand::Register(Register::CF);
    //         let of     = Operand::Register(Register::OF);

    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(1, bvSize)),
    //                       self.ast_ctxt.bvxor(
    //                         self.ast_ctxt.extract(high, high, op1),
    //                         self.symbolicEngine.getOperandAst(inst, cf)
    //                       ),
    //                       self.symbolicEngine.getOperandAst(of)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, of.getConstRegister(), "Overflow flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(of.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeReadRegister(cf.getConstRegister());
    //           inst.removeWrittenRegister(of.getConstRegister());
    //         }
    //       }

    //       fn ofSar_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let of     = Operand::Register(Register::OF);

    //         /*
    //          * Create the semantic.
    //          * of = 0 if op2 == 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.land(
    //                         self.ast_ctxt.equal(
    //                           /* #672 */
    //                           Operand::Instruction(parent),
    //                           Operand::Instruction(parent)
    //                           /* ---- */
    //                         ),
    //                         self.ast_ctxt.equal(
    //                           op2,
    //                           self.ast_ctxt.bv(1, bvSize)
    //                         )
    //                       ),
    //                       self.ast_ctxt.bv(0, 1),
    //                       self.symbolicEngine.getOperandAst(of)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, of.getConstRegister(), "Overflow flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(of.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(of.getConstRegister());
    //         }
    //       }

    //       fn ofShl_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let of     = Operand::Register(Register::OF);

    //         /*
    //          * Create the semantic.
    //          * of = ((op1 >> (bvSize - 1)) ^ (op1 >> (bvSize - 2))) & 1; if op2 == 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         op2,
    //                         self.ast_ctxt.bv(1, bvSize)),
    //                       self.ast_ctxt.extract(0, 0,
    //                         self.ast_ctxt.bvxor(
    //                           self.ast_ctxt.bvlshr(op1, self.ast_ctxt.bvsub(self.ast_ctxt.bv(bvSize, bvSize), self.ast_ctxt.bv(1, bvSize))),
    //                           self.ast_ctxt.bvlshr(op1, self.ast_ctxt.bvsub(self.ast_ctxt.bv(bvSize, bvSize), self.ast_ctxt.bv(2, bvSize)))
    //                         )
    //                       ),
    //                       self.symbolicEngine.getOperandAst(of)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, of.getConstRegister(), "Overflow flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(of.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(of.getConstRegister());
    //         }
    //       }

    //       fn ofShld_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   op2: Operand,
    //                                   op3: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize  = dst.get_bit_size();
    //         let bv1Size = op1.getBitvectorSize();
    //         let bv2Size = op2.getBitvectorSize();
    //         let bv3Size = op3.getBitvectorSize();
    //         let of      = Operand::Register(Register::OF);

    //         /*
    //          * Create the semantic.
    //          * of = MSB(rol(op3, concat(op2,op1))) ^ MSB(op1); if op3 == 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.zx(bvSize - bv3Size, op3),
    //                         self.ast_ctxt.bv(1, bvSize)),
    //                       self.ast_ctxt.bvxor(
    //                         self.ast_ctxt.extract(
    //                           bvSize-1, bvSize-1,
    //                           self.ast_ctxt.bvrol(
    //                             self.ast_ctxt.concat(op2, op1),
    //                             self.ast_ctxt.zx(((bv1Size + bv2Size) - bv3Size), op3)
    //                           )
    //                         ),
    //                         self.ast_ctxt.extract(bvSize-1, bvSize-1, op1)
    //                       ),
    //                       self.symbolicEngine.getOperandAst(of)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, of.getConstRegister(), "Overflow flag");

    //         if (op3.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(of.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(of.getConstRegister());
    //         }
    //       }

    //       fn ofShr_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op1: Operand,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let of     = Operand::Register(Register::OF);

    //         /*
    //          * Create the semantic.
    //          * of = ((op1 >> (bvSize - 1)) & 1) if op2 == 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         op2,
    //                         self.ast_ctxt.bv(1, bvSize)),
    //                       self.ast_ctxt.extract(0, 0, self.ast_ctxt.bvlshr(op1, self.ast_ctxt.bvsub(self.ast_ctxt.bv(bvSize, bvSize), self.ast_ctxt.bv(1, bvSize)))),
    //                       self.symbolicEngine.getOperandAst(of)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, of.getConstRegister(), "Overflow flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(of.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(of.getConstRegister());
    //         }
    //       }

    //       fn ofShrd_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   op2: Operand,
    //                                   op3: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize  = dst.get_bit_size();
    //         let bv1Size = op1.getBitvectorSize();
    //         let bv2Size = op2.getBitvectorSize();
    //         let bv3Size = op3.getBitvectorSize();
    //         let of      = Operand::Register(Register::OF);

    //         /*
    //          * Create the semantic.
    //          * of = MSB(ror(op3, concat(op2,op1))) ^ MSB(op1); if op3 == 1
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.zx(bvSize - op3.getBitvectorSize(), op3),
    //                         self.ast_ctxt.bv(1, bvSize)),
    //                       self.ast_ctxt.bvxor(
    //                         self.ast_ctxt.extract(
    //                           bvSize - 1, bvSize - 1,
    //                           self.ast_ctxt.bvror(
    //                             self.ast_ctxt.concat(op2, op1),
    //                             self.ast_ctxt.zx(((bv1Size + bv2Size) - bv3Size), op3)
    //                           )
    //                         ),
    //                         self.ast_ctxt.extract(dst.get_bit_size()-1, dst.get_bit_size()-1, op1)
    //                       ),
    //                       self.symbolicEngine.getOperandAst(of)
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, of.getConstRegister(), "Overflow flag");

    //         if (op3.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(of.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(of.getConstRegister());
    //         }
    //       }

    fn ofSub_s(
        &mut self,
        inst: x86Instruction,
        parent: InstructionIdx,
        dst: OperandWrapper,
        op1: Operand,
        op2: Operand,
    ) {
        // todo: optional arg
        let vol: bool = false;

        let bvSize = dst.get_bit_size();
        let low = if vol { 0 } else { dst.get_low() };
        let high = if vol { bvSize - 1 } else { dst.get_high() };

        /*
         * Create the semantic.
         * of = high:bool((op1 ^ op2) & (op1 ^ regDst))
         */
        let node = self.ast_ctxt.extract(
            bvSize - 1,
            bvSize - 1,
            Operand::Instruction(self.ast_ctxt.bvand(
                Operand::Instruction(self.ast_ctxt.bvxor(op1, op2)),
                Operand::Instruction(self.ast_ctxt.bvxor(
                    op1,
                    Operand::Instruction(self.ast_ctxt.extract(
                        high,
                        low,
                        Operand::Instruction(parent),
                    )),
                )),
            )),
        );

        /* Create the symbolic expression */
        // let expr =
        //     self.symbolicEngine
        //         .createSymbolicExpression(inst, node, Register::OF, "Overflow flag");

        /* Spread the taint from the parent to the child */
        // expr.isTainted = self.taintEngine.setTaintRegister(Register::OF, parent.isTainted);
    }

    fn pf_s(&mut self, inst: x86Instruction, parent: InstructionIdx, dst: OperandWrapper) {
        // todo: optional arg
        let vol: bool = false;

        let low = if vol { 0 } else { dst.get_low() };
        let high = if vol {
            BitSizes::BYTE - 1
        } else if low == 0 {
            BitSizes::BYTE - 1
        } else {
            BitSizes::WORD - 1
        };

        /*
         * Create the semantics.
         *
         * pf is set to one if there is an even number of bit set to 1 in the least
         * significant byte of the result.
         */
        let mut node = self.ast_ctxt.bv(1, 1);
        for counter in 0..=BitSizes::BYTE - 1 {
            node = self.ast_ctxt.bvxor(
                Operand::Instruction(node),
                Operand::Instruction(self.ast_ctxt.extract(
                    counter,
                    counter,
                    Operand::Instruction(parent),
                )),
            );
        }

        /* Create the symbolic expression */
        // let expr =
        //     self.symbolicEngine
        //         .createSymbolicExpression(inst, node, Register::PF, "Parity flag");

        /* Spread the taint from the parent to the child */
        // expr.isTainted = self.taintEngine.setTaintRegister(Register::PF, parent.isTainted);
    }

    //       fn pfShl_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let low = if vol { 0 } else { dst.get_low() };
    //         let high   = if vol { BitSizes::BYTE-1 } else if !low { BitSizes::BYTE-1 } else { BitSizes::WORD-1 };
    //         let pf     = Operand::Register(Register::PF);

    //         /*
    //          * Create the semantics.
    //          * pf if op2 != 0
    //          */
    //         let node1 = self.ast_ctxt.bv(1, 1);
    //         for counter in 0..=BitSizes::BYTE-1 {
    //             node1 = self.ast_ctxt.bvxor(node1, self.ast_ctxt.extract(counter, counter, Operand::Instruction(parent)));
    //         }

    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(self.ast_ctxt.zx(bvSize - op2.getBitvectorSize(), op2), self.ast_ctxt.bv(0, bvSize)),
    //                        self.symbolicEngine.getOperandAst(pf),
    //                        node1
    //                      );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node2, pf.getConstRegister(), "Parity flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(pf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(pf.getConstRegister());
    //         }
    //       }

    fn sf_s(&mut self, inst: x86Instruction, parent: InstructionIdx, dst: OperandWrapper) {
        // todo: optional arg
        let vol: bool = false;

        let bvSize = dst.get_bit_size();
        let high = if vol { bvSize - 1 } else { dst.get_high() };

        /*
         * Create the semantic.
         * sf = high:bool(regDst)
         */
        let node = self
            .ast_ctxt
            .extract(high, high, Operand::Instruction(parent));

        /* Create the symbolic expression */
        // let expr =
        //     self.symbolicEngine
        //         .createSymbolicExpression(inst, node, Register::SF, "Sign flag");

        /* Spread the taint from the parent to the child */
        // expr.isTainted = self.taintEngine.setTaintRegister(Register::SF, parent.isTainted);
    }

    //       fn sfShl_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};
    //         let sf     = Operand::Register(Register::SF);

    //         /*
    //          * Create the semantic.
    //          * sf if op2 != 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(sf),
    //                       self.ast_ctxt.extract(high, high, Operand::Instruction(parent))
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, sf.getConstRegister(), "Sign flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(sf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(sf.getConstRegister());
    //         }
    //       }

    //       fn sfShld_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   op2: Operand,
    //                                   op3: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize  = dst.get_bit_size();
    //         let bv1Size = op1.getBitvectorSize();
    //         let bv2Size = op2.getBitvectorSize();
    //         let bv3Size = op3.getBitvectorSize();
    //         let sf      = Operand::Register(Register::SF);

    //         /*
    //          * Create the semantic.
    //          * MSB(rol(op3, concat(op2,op1))) if op3 != 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op3, self.ast_ctxt.bv(0, bv3Size)),
    //                       self.symbolicEngine.getOperandAst(sf),
    //                       self.ast_ctxt.extract(
    //                         bvSize-1, bvSize-1,
    //                         self.ast_ctxt.bvrol(
    //                           self.ast_ctxt.concat(op2, op1),
    //                           self.ast_ctxt.zx(((bv1Size + bv2Size) - bv3Size), op3)
    //                         )
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, sf.getConstRegister(), "Sign flag");

    //         if (op3.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(sf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(sf.getConstRegister());
    //         }
    //       }

    //       fn sfShrd_s(&mut self, inst: x86Instruction,
    //                                   parent: InstructionIdx,
    //                                   dst: OperandWrapper,
    //                                   op1: Operand,
    //                                   op2: Operand,
    //                                   op3: Operand,
    //                                   ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize  = dst.get_bit_size();
    //         let bv1Size = op1.getBitvectorSize();
    //         let bv2Size = op2.getBitvectorSize();
    //         let bv3Size = op3.getBitvectorSize();
    //         let sf      = Operand::Register(Register::SF);

    //         /*
    //          * Create the semantic.
    //          * MSB(ror(op3, concat(op2,op1))) if op3 != 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op3, self.ast_ctxt.bv(0, bv3Size)),
    //                       self.symbolicEngine.getOperandAst(sf),
    //                       self.ast_ctxt.extract(
    //                         bvSize - 1, bvSize - 1,
    //                         self.ast_ctxt.bvror(
    //                           self.ast_ctxt.concat(op2, op1),
    //                           self.ast_ctxt.zx(((bv1Size + bv2Size) - bv3Size), op3)
    //                         )
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, sf.getConstRegister(), "Sign flag");

    //         if (op3.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(sf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(sf.getConstRegister());
    //         }
    //       }

    fn zf_s(&mut self, inst: x86Instruction, parent: InstructionIdx, dst: OperandWrapper) {
        // todo: optional arg
        let vol: bool = false;

        let bvSize = dst.get_bit_size();
        let low = if vol { 0 } else { dst.get_low() };
        let high = if vol { bvSize - 1 } else { dst.get_high() };

        /*
         * Create the semantic.
         * zf = 0 == regDst
         */
        let node = self.ast_ctxt.ite(
            Operand::Instruction(self.ast_ctxt.equal(
                Operand::Instruction(self.ast_ctxt.extract(
                    high,
                    low,
                    Operand::Instruction(parent),
                )),
                Operand::Instruction(self.ast_ctxt.bv(0, bvSize)),
            )),
            Operand::Instruction(self.ast_ctxt.bv(1, 1)),
            Operand::Instruction(self.ast_ctxt.bv(0, 1)),
        );

        // /* Create the symbolic expression */
        // let expr =
        //     self.symbolicEngine
        //         .createSymbolicExpression(inst, node, Register::ZF, "Zero flag");

        /* Spread the taint from the parent to the child */
        // expr.isTainted = self.taintEngine.setTaintRegister(Register::ZF, parent.isTainted);
    }

    //       fn zfBsf_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  src: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         /*
    //          * Create the semantic.
    //          * zf = 1 if op2 == 0 else 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, src.get_bit_size())),
    //                       self.ast_ctxt.bvtrue(),
    //                       self.ast_ctxt.bvfalse()
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::ZF, "Zero flag");

    //         /* Spread the taint from the parent to the child */
    //         // expr.isTainted = self.taintEngine.setTaintRegister(Register::ZF, parent.isTainted);
    //       }

    //       fn zfShl_s(&mut self, inst: x86Instruction,
    //                                  parent: InstructionIdx,
    //                                  dst: OperandWrapper,
    //                                  op2: Operand,
    //                                  ) {
    //                                     // todo: optional arg
    //                                     let vol: bool = false;

    //         let bvSize = dst.get_bit_size();
    //         let low = if vol { 0 } else { dst.get_low() };
    //         let high   = if vol  {bvSize-1 }else {dst.get_high()};
    //         let zf     = Operand::Register(Register::ZF);

    //         /*
    //          * Create the semantic.
    //          * zf if op2 != 0
    //          */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(self.ast_ctxt.zx(bvSize - op2.getBitvectorSize(), op2), self.ast_ctxt.bv(0, bvSize)),
    //                       self.symbolicEngine.getOperandAst(zf),
    //                       self.ast_ctxt.ite(
    //                         self.ast_ctxt.equal(
    //                           self.ast_ctxt.extract(high, low, Operand::Instruction(parent)),
    //                           self.ast_ctxt.bv(0, bvSize)
    //                         ),
    //                         self.ast_ctxt.bv(1, 1),
    //                         self.ast_ctxt.bv(0, 1)
    //                       )
    //                     );

    //         /* Create the symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, zf.getConstRegister(), "Zero flag");

    //         if (op2.evaluate()) {
    //           /* Spread the taint from the parent to the child */
    //         //   expr.isTainted = self.taintEngine.setTaintRegister(zf.getConstRegister(), parent.isTainted);
    //         }
    //         else {
    //           inst.removeWrittenRegister(zf.getConstRegister());
    //         }
    //       }

    //       fn aaa_s(&mut self, inst: x86Instruction) {
    //         let  src1   = Operand::Register(Register::AL);
    //         let  src2   = Operand::Register(Register::AH);
    //         let  src3   = Operand::Register(Register::AF);
    //         let  dst    = Operand::Register(Register::AX);
    //         let  dsttmp = Operand::Register(Register::AL);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src3);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       // if
    //                       self.ast_ctxt.lor(
    //                         self.ast_ctxt.bvugt(
    //                           self.ast_ctxt.bvand(op1, self.ast_ctxt.bv(0xf, src1.get_bit_size())),
    //                           self.ast_ctxt.bv(9, src1.get_bit_size())
    //                         ),
    //                         self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue())
    //                       ),
    //                       // then
    //                       self.ast_ctxt.concat(
    //                         self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(1, src2.get_bit_size())),
    //                         self.ast_ctxt.bvand(
    //                           self.ast_ctxt.bvadd(op1, self.ast_ctxt.bv(6, src1.get_bit_size())),
    //                           self.ast_ctxt.bv(0xf, src1.get_bit_size())
    //                         )
    //                       ),
    //                       // else
    //                       self.ast_ctxt.concat(
    //                         op2,
    //                         self.ast_ctxt.bvand(op1, self.ast_ctxt.bv(0xf, src1.get_bit_size()))
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "AAA operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Update symbolic flags */
    //         self.afAaa_s(inst, expr, dsttmp, op1, op3);
    //         self.cfAaa_s(inst, expr, dsttmp, op1, op3);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);
    //         self.undefined_s(inst, Register::ZF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn aad_s(&mut self, inst: x86Instruction) {
    //         let  src1   = triton::arch::OperandWrapper(triton::arch::Immediate(0x0a, ByteSizes::BYTE)); /* D5 0A */
    //         let  src2   = Operand::Register(Register::AL);
    //         let  src3   = Operand::Register(Register::AH);
    //         let  dst    = Operand::Register(Register::AX);
    //         let  dsttmp = Operand::Register(Register::AL);

    //         /* D5 ib */
    //         if (inst.operands.size() == 1){
    //           src1 = inst.operands[0];
    // }
    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src3);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.zx(
    //                       BitSizes::BYTE,
    //                       self.ast_ctxt.bvadd(
    //                         op2,
    //                         self.ast_ctxt.bvmul(op3, op1)
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "AAD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Update symbolic flags */
    //         self.pf_s(inst, expr, dsttmp);
    //         self.sf_s(inst, expr, dsttmp);
    //         self.zf_s(inst, expr, dsttmp);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::CF);
    //         self.undefined_s(inst, Register::OF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn aam_s(&mut self, inst: x86Instruction) {
    //         let  src1   = triton::arch::OperandWrapper(triton::arch::Immediate(0x0a, ByteSizes::BYTE)); /* D4 0A */
    //         let  src2   = Operand::Register(Register::AL);
    //         let  dst    = Operand::Register(Register::AX);
    //         let  dsttmp = Operand::Register(Register::AL);

    //         /* D4 ib */
    //         if (inst.operands.size() == 1){
    //           src1 = inst.operands[0];
    // }
    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.concat(
    //                       self.ast_ctxt.bvudiv(op2, op1),
    //                       self.ast_ctxt.bvurem(op2, op1)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "AAM operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Update symbolic flags */
    //         self.pf_s(inst, expr, dsttmp);
    //         self.sf_s(inst, expr, dsttmp);
    //         self.zf_s(inst, expr, dsttmp);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::CF);
    //         self.undefined_s(inst, Register::OF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn aas_s(&mut self, inst: x86Instruction) {
    //         let  src1   = Operand::Register(Register::AL);
    //         let  src2   = Operand::Register(Register::AH);
    //         let  src3   = Operand::Register(Register::AF);
    //         let  dst    = Operand::Register(Register::AX);
    //         let  dsttmp = Operand::Register(Register::AL);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src3);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       // if
    //                       self.ast_ctxt.lor(
    //                         self.ast_ctxt.bvugt(
    //                           self.ast_ctxt.bvand(op1, self.ast_ctxt.bv(0xf, src1.get_bit_size())),
    //                           self.ast_ctxt.bv(9, src1.get_bit_size())
    //                         ),
    //                         self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue())
    //                       ),
    //                       // then
    //                       self.ast_ctxt.concat(
    //                         self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(1, src2.get_bit_size())),
    //                         self.ast_ctxt.bvand(
    //                           self.ast_ctxt.bvsub(op1, self.ast_ctxt.bv(6, src1.get_bit_size())),
    //                           self.ast_ctxt.bv(0xf, src1.get_bit_size())
    //                         )
    //                       ),
    //                       // else
    //                       self.ast_ctxt.concat(
    //                         op2,
    //                         self.ast_ctxt.bvand(op1, self.ast_ctxt.bv(0xf, src1.get_bit_size()))
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "AAS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Update symbolic flags */
    //         self.afAaa_s(inst, expr, dsttmp, op1, op3);
    //         self.cfAaa_s(inst, expr, dsttmp, op1, op3);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);
    //         self.undefined_s(inst, Register::ZF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn adc_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  cf  = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, cf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvadd(self.ast_ctxt.bvadd(op1, op2), self.ast_ctxt.zx(dst.get_bit_size()-1, op3));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ADC operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, cf);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr, dst, op1, op2);
    //         self.cfAdd_s(inst, expr, dst, op1, op2);
    //         self.ofAdd_s(inst, expr, dst, op1, op2);
    //         self.pf_s(inst, expr, dst);
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn adcx_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  cf  = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, cf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvadd(self.ast_ctxt.bvadd(op1, op2), self.ast_ctxt.zx(dst.get_bit_size()-1, op3));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ADCX operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, cf);

    //         /* Update symbolic flags */
    //         self.cfAdd_s(inst, expr, dst, op1, op2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn add_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvadd(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ADD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr, dst, op1, op2);
    //         self.cfAdd_s(inst, expr, dst, op1, op2);
    //         self.ofAdd_s(inst, expr, dst, op1, op2);
    //         self.pf_s(inst, expr, dst);
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn and_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "AND operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update symbolic flags */
    //         self.clearFlag_s(inst, Register::CF, "Clears carry flag");
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.pf_s(inst, expr, dst);
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn andn_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(self.ast_ctxt.bvnot(op2), op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ANDN operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         self.clearFlag_s(inst, Register::CF, "Clears carry flag");
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn andnpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(self.ast_ctxt.bvnot(op1), op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ANDNPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn andnps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(self.ast_ctxt.bvnot(op1), op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ANDNPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn andpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ANDPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn andps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ANDPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn bextr_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(
    //                       self.ast_ctxt.bvlshr(
    //                         op1,
    //                         self.ast_ctxt.zx(src1.get_bit_size() - BitSizes::BYTE, self.ast_ctxt.extract(7, 0, op2))
    //                       ),
    //                       self.ast_ctxt.bvsub(
    //                         self.ast_ctxt.bvshl(
    //                           self.ast_ctxt.bv(1, src1.get_bit_size()),
    //                           self.ast_ctxt.zx(src1.get_bit_size() - BitSizes::BYTE, self.ast_ctxt.extract(15, 8, op2))
    //                         ),
    //                         self.ast_ctxt.bv(1, src1.get_bit_size())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "BEXTR operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update symbolic flags */
    //         self.clearFlag_s(inst, Register::CF, "Clears carry flag");
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn blsi_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(self.ast_ctxt.bvneg(op1), op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "BLSI operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update symbolic flags */
    //         self.cfBlsi_s(inst, expr, src, op1);
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn blsmsk_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvxor(
    //                       self.ast_ctxt.bvsub(op1, self.ast_ctxt.bv(1, src.get_bit_size())),
    //                       op1
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "BLSMSK operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update symbolic flags */
    //         self.cfBlsmsk_s(inst, expr, src, op1);
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.sf_s(inst, expr, dst);
    //         self.clearFlag_s(inst, Register::ZF, "Clears zero flag");

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn blsr_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(
    //                       self.ast_ctxt.bvsub(op1, self.ast_ctxt.bv(1, src.get_bit_size())),
    //                       op1
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "BLSR operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update symbolic flags */
    //         self.cfBlsr_s(inst, expr, src, op1);
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn bsf_s(&mut self, inst: x86Instruction) {
    //         let dst     = inst.operands[0];
    //         let src     = inst.operands[1];
    //         let  bvSize1 = dst.get_bit_size();
    //         let  bvSize2 = src.get_bit_size();

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction;
    //         match src.getSize() {
    //           ByteSizes::BYTE => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize2)), /* Apply BSF only if op2 != 0 */
    //                      op1,
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))
    //                    );
    //                 }
    //           ByteSizes::WORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize2)), /* Apply BSF only if op2 != 0 */
    //                      op1,
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))
    //                    );
    //                 }
    //           ByteSizes::DWORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize2)), /* Apply BSF only if op2 != 0 */
    //                      op1,
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(16, 16, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(16, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(17, 17, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(17, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(18, 18, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(18, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(19, 19, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(19, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(20, 20, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(20, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(21, 21, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(21, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(22, 22, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(22, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(23, 23, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(23, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(24, 24, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(24, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(25, 25, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(25, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(26, 26, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(26, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(27, 27, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(27, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(28, 28, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(28, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(29, 29, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(29, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(30, 30, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(30, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(31, 31, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(31, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))))))))))))))))))
    //                    );
    //                 }
    //           ByteSizes::QWORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize2)), /* Apply BSF only if op2 != 0 */
    //                      op1,
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(16, 16, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(16, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(17, 17, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(17, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(18, 18, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(18, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(19, 19, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(19, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(20, 20, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(20, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(21, 21, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(21, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(22, 22, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(22, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(23, 23, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(23, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(24, 24, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(24, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(25, 25, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(25, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(26, 26, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(26, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(27, 27, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(27, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(28, 28, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(28, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(29, 29, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(29, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(30, 30, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(30, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(31, 31, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(31, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(32, 32, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(32, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(33, 33, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(33, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(34, 34, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(34, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(35, 35, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(35, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(36, 36, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(36, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(37, 37, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(37, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(38, 38, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(38, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(39, 39, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(39, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(40, 40, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(40, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(41, 41, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(41, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(42, 42, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(42, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(43, 43, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(43, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(44, 44, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(44, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(45, 45, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(45, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(46, 46, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(46, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(47, 47, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(47, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(48, 48, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(48, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(49, 49, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(49, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(50, 50, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(50, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(51, 51, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(51, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(52, 52, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(52, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(53, 53, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(53, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(54, 54, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(54, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(55, 55, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(55, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(56, 56, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(56, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(57, 57, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(57, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(58, 58, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(58, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(59, 59, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(59, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(60, 60, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(60, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(61, 61, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(61, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(62, 62, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(62, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(63, 63, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(63, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    //                    );
    //                 }
    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::bsf_s(): Invalid operand size.");"#),
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "BSF operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update symbolic flags */
    //         self.zfBsf_s(inst, expr, src, op2);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::CF);
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn bsr_s(&mut self, inst: x86Instruction) {
    //         let dst     = inst.operands[0];
    //         let src     = inst.operands[1];
    //         let  bvSize1 = dst.get_bit_size();
    //         let  bvSize2 = src.get_bit_size();

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction;
    //         match src.getSize() {
    //           ByteSizes::BYTE => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize2)), /* Apply BSR only if op2 != 0 */
    //                      op1,
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))
    //                    );
    //             }
    //           ByteSizes::WORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize2)), /* Apply BSR only if op2 != 0 */
    //                      op1,
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))
    //                    );
    //             }
    //           ByteSizes::DWORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize2)), /* Apply BSR only if op2 != 0 */
    //                      op1,
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(31, 31, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(31, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(30, 30, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(30, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(29, 29, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(29, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(28, 28, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(28, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(27, 27, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(27, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(26, 26, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(26, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(25, 25, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(25, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(24, 24, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(24, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(23, 23, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(23, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(22, 22, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(22, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(21, 21, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(21, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(20, 20, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(20, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(19, 19, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(19, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(18, 18, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(18, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(17, 17, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(17, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(16, 16, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(16, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))))))))))))))))))
    //                    );
    //             }
    //           ByteSizes::QWORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, bvSize2)), /* Apply BSR only if op2 != 0 */
    //                      op1,
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(63, 63, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(63, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(62, 62, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(62, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(61, 61, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(61, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(60, 60, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(60, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(59, 59, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(59, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(58, 58, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(58, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(57, 57, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(57, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(56, 56, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(56, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(55, 55, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(55, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(54, 54, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(54, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(53, 53, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(53, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(52, 52, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(52, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(51, 51, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(51, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(50, 50, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(50, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(49, 49, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(49, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(48, 48, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(48, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(47, 47, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(47, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(46, 46, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(46, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(45, 45, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(45, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(44, 44, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(44, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(43, 43, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(43, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(42, 42, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(42, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(41, 41, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(41, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(40, 40, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(40, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(39, 39, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(39, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(38, 38, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(38, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(37, 37, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(37, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(36, 36, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(36, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(35, 35, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(35, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(34, 34, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(34, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(33, 33, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(33, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(32, 32, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(32, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(31, 31, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(31, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(30, 30, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(30, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(29, 29, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(29, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(28, 28, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(28, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(27, 27, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(27, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(26, 26, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(26, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(25, 25, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(25, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(24, 24, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(24, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(23, 23, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(23, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(22, 22, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(22, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(21, 21, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(21, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(20, 20, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(20, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(19, 19, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(19, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(18, 18, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(18, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(17, 17, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(17, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(16, 16, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(16, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op2), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    //                    );
    //             }
    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::bsr_s(): Invalid operand size.");"#)
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "BSR operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update symbolic flags */
    //         self.zfBsf_s(inst, expr, src, op2); /* same as bsf */
    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::CF);
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn bswap_s(&mut self, inst: x86Instruction) {
    //         let src = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         std::list<triton::ast::SharedAbstractNode> bytes;
    //         match src.getSize() {
    //           ByteSizes::QWORD => {
    //             bytes.push_front(self.ast_ctxt.extract(63, 56, op1));
    //             bytes.push_front(self.ast_ctxt.extract(55, 48, op1));
    //             bytes.push_front(self.ast_ctxt.extract(47, 40, op1));
    //             bytes.push_front(self.ast_ctxt.extract(39, 32, op1));

    //             // todo: duplicated below
    //             bytes.push_front(self.ast_ctxt.extract(31, 24, op1));
    //             bytes.push_front(self.ast_ctxt.extract(23, 16, op1));
    //             bytes.push_front(self.ast_ctxt.extract(15, 8, op1));
    //             bytes.push_front(self.ast_ctxt.extract(7,  0, op1));
    //           }

    //           ByteSizes::DWORD => {
    //             bytes.push_front(self.ast_ctxt.extract(31, 24, op1));
    //             bytes.push_front(self.ast_ctxt.extract(23, 16, op1));
    //             bytes.push_front(self.ast_ctxt.extract(15, 8, op1));
    //             bytes.push_front(self.ast_ctxt.extract(7,  0, op1));
    //           }
    //           ByteSizes::WORD => {
    //             // See #1131
    //             bytes.push_front(self.ast_ctxt.bv(0, 8));
    //             bytes.push_front(self.ast_ctxt.bv(0, 8));
    //           }
    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::bswap_s(): Invalid operand size.");"#)
    //         }

    //         let node = self.ast_ctxt.concat(bytes);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, src, "BSWAP operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(src, src);

    //         /* Tag undefined registers */
    //         if (src.getSize() == ByteSizes::WORD) {
    //           // When the BSWAP instruction references a 16-bit register, the result is undefined.
    //           self.undefined_s(inst, src.getRegister());
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn bt_s(&mut self, inst: x86Instruction) {
    //         let  dst  = Operand::Register(Register::CF);
    //         let src1 = inst.operands[0];
    //         let src2 = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.ast_ctxt.zx(src1.get_bit_size() - src2.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src2));

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.extract(0, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op1,
    //                         self.ast_ctxt.bvsmod(
    //                           op2,
    //                           self.ast_ctxt.bv(src1.get_bit_size(), src1.get_bit_size())
    //                         )
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, Register::CF, "BT operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src1);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src2);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn btc_s(&mut self, inst: x86Instruction) {
    //         let  dst1 = Operand::Register(Register::CF);
    //         let dst2 = inst.operands[0];
    //         let src1 = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst2);
    //         let op2 = self.ast_ctxt.zx(dst2.get_bit_size() - src1.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src1));

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.extract(0, 0,
    //                        self.ast_ctxt.bvlshr(
    //                          op1,
    //                          self.ast_ctxt.bvsmod(
    //                            op2,
    //                            self.ast_ctxt.bv(dst2.get_bit_size(), dst2.get_bit_size())
    //                          )
    //                        )
    //                      );
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(node1, self.ast_ctxt.bvfalse()),
    //                        /* BTS */
    //                        self.ast_ctxt.bvor(
    //                          op1,
    //                          self.ast_ctxt.bvshl(
    //                            self.ast_ctxt.bv(1, dst2.get_bit_size()),
    //                            self.ast_ctxt.bvsmod(
    //                              op2,
    //                              self.ast_ctxt.bv(dst2.get_bit_size(), dst2.get_bit_size())
    //                            )
    //                          )
    //                        ),
    //                        /* BTR */
    //                        self.ast_ctxt.bvand(
    //                          op1,
    //                          self.ast_ctxt.bvsub(
    //                            op1,
    //                            self.ast_ctxt.bvshl(
    //                              self.ast_ctxt.bv(1, dst2.get_bit_size()),
    //                              self.ast_ctxt.bvsmod(
    //                                op2,
    //                                self.ast_ctxt.bv(dst2.get_bit_size(), dst2.get_bit_size())
    //                              )
    //                            )
    //                          )
    //                        )
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, Register::CF, "BTC carry operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2, "BTC complement operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintUnion(dst1, dst2);
    //         // expr1.isTainted = self.taintEngine.taintUnion(dst1, src1);
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst2, src1);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn btr_s(&mut self, inst: x86Instruction) {
    //         let  dst1 = Operand::Register(Register::CF);
    //         let dst2 = inst.operands[0];
    //         let src1 = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst2);
    //         let op2 = self.ast_ctxt.zx(dst2.get_bit_size() - src1.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src1));

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.extract(0, 0,
    //                        self.ast_ctxt.bvlshr(
    //                          op1,
    //                          self.ast_ctxt.bvsmod(
    //                            op2,
    //                            self.ast_ctxt.bv(dst2.get_bit_size(), dst2.get_bit_size())
    //                          )
    //                        )
    //                      );
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(node1, self.ast_ctxt.bvfalse()),
    //                        op1,
    //                        self.ast_ctxt.bvand(
    //                          op1,
    //                          self.ast_ctxt.bvsub(
    //                            op1,
    //                            self.ast_ctxt.bvshl(
    //                              self.ast_ctxt.bv(1, dst2.get_bit_size()),
    //                              self.ast_ctxt.bvsmod(
    //                                op2,
    //                                self.ast_ctxt.bv(dst2.get_bit_size(), dst2.get_bit_size())
    //                              )
    //                            )
    //                          )
    //                        )
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, Register::CF, "BTR carry operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2, "BTR reset operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintUnion(dst1, dst2);
    //         // expr1.isTainted = self.taintEngine.taintUnion(dst1, src1);
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst2, src1);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn bts_s(&mut self, inst: x86Instruction) {
    //         let  dst1 = Operand::Register(Register::CF);
    //         let dst2 = inst.operands[0];
    //         let src1 = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst2);
    //         let op2 = self.ast_ctxt.zx(dst2.get_bit_size() - src1.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src1));

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.extract(0, 0,
    //                        self.ast_ctxt.bvlshr(
    //                          op1,
    //                          self.ast_ctxt.bvsmod(
    //                            op2,
    //                            self.ast_ctxt.bv(dst2.get_bit_size(), dst2.get_bit_size())
    //                          )
    //                        )
    //                      );
    //         let node2 = self.ast_ctxt.bvor(
    //                        op1,
    //                        self.ast_ctxt.bvshl(
    //                          self.ast_ctxt.bv(1, dst2.get_bit_size()),
    //                          self.ast_ctxt.bvsmod(
    //                            op2,
    //                            self.ast_ctxt.bv(dst2.get_bit_size(), dst2.get_bit_size())
    //                          )
    //                        )
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, Register::CF, "BTS carry operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2, "BTS set operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintUnion(dst1, dst2);
    //         // expr1.isTainted = self.taintEngine.taintUnion(dst1, src1);
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst2, src1);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn call_s(&mut self, inst: x86Instruction) {
    //         let src        = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics - side effect */
    //         let stack      = self.architecture.get_stack_pointer();
    //         let stackValue = alignSubStack_s(inst, stack.getSize());
    //         let pc         = Operand::Register(self.architecture.get_program_counter());
    //         let sp         = Operand::Memory(MemoryAccess::new(stackValue, stack.getSize()));

    //         let node1 = self.ast_ctxt.bv(inst.next_ip(), pc.get_bit_size());

    //         /* Create the semantics */
    //         let node2 = op1;

    //         /* Create the symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, sp, "Saved Program Counter");

    //         /* Create symbolic expression */
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, pc, "Program Counter");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.untaintMemory(sp.getMemory());
    //         // expr2.isTainted = self.taintEngine.taintAssignment(pc, src);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr2);
    //       }

    //       fn cbw_s(&mut self, inst: x86Instruction) {
    //         let dst = Operand::Register(Register::AX);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.sx(BitSizes::BYTE, self.ast_ctxt.extract(BitSizes::BYTE-1, 0, op1));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CBW operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cdq_s(&mut self, inst: x86Instruction) {
    //         let dst = Operand::Register(Register::EDX);
    //         let src = Operand::Register(Register::EAX);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics - TMP = 64 bitvec (EDX:EAX) */
    //         let node1 = self.ast_ctxt.sx(BitSizes::DWORD, op1);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "Temporary variable");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.isRegisterTainted(Register::EAX);

    //         /* Create the semantics - EDX = TMP[63...32] */
    //         let node2 = self.ast_ctxt.extract(BitSizes::QWORD-1, BitSizes::DWORD, self.ast_ctxt.reference(expr1));

    //         /* Create symbolic expression */
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst, "CDQ operation");

    //         /* Spread taint */
    //         // expr2.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cdqe_s(&mut self, inst: x86Instruction) {
    //         let dst = Operand::Register(Register::RAX);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.sx(BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op1));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CDQE operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn clc_s(&mut self, inst: x86Instruction) {
    //         self.clearFlag_s(inst, Register::CF, "Clears carry flag");
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cld_s(&mut self, inst: x86Instruction) {
    //         self.clearFlag_s(inst, Register::DF, "Clears direction flag");
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn clflush_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn clts_s(&mut self, inst: x86Instruction) {
    //         let dst = Operand::Register(Register::CR0);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);

    //         /* Create the semantics */
    //         let mut node: Instruction;

    //         match dst.get_bit_size() {
    //           BitSizes::QWORD =>
    //             node = self.ast_ctxt.bvand(op1, self.ast_ctxt.bv(0xfffffffffffffff7, BitSizes::QWORD)),
    //           BitSizes::DWORD =>
    //             node = self.ast_ctxt.bvand(op1, self.ast_ctxt.bv(0xfffffff7, BitSizes::DWORD)),
    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::clts_s(): Invalid operand size.");"#)
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CLTS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cli_s(&mut self, inst: x86Instruction) {
    //         self.clearFlag_s(inst, Register::IF, "Clears interrupt flag");
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmc_s(&mut self, inst: x86Instruction) {
    //         let dst = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvnot(op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst.getRegister(), "CMC operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmova_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  cf  = Operand::Register(Register::CF);
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, cf);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvand(self.ast_ctxt.bvnot(op3), self.ast_ctxt.bvnot(op4)), self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVA operation");

    //         /* Spread taint and condition flag */
    //         if (op3.evaluate().is_zero() && op4.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // // expr.isTainted |= self.taintEngine.isTainted(cf) || self.taintEngine.isTainted(zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovae_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  cf  = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, cf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVAE operation");

    //         /* Spread taint and condition flag */
    //         if (op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(cf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  cf  = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, cf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVB operation");

    //         /* Spread taint and condition flag */
    //         if (!op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(cf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovbe_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  cf  = Operand::Register(Register::CF);
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, cf);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvor(op3, op4), self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVBE operation");

    //         /* Spread taint and condition flag */
    //         if (!op3.evaluate().is_zero() || !op4.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // // expr.isTainted |= self.taintEngine.isTainted(cf) || self.taintEngine.isTainted(zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmove_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVE operation");

    //         /* Spread taint and condition flag */
    //         if (!op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovg_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  sf  = Operand::Register(Register::SF);
    //         let  of  = Operand::Register(Register::OF);
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvor(self.ast_ctxt.bvxor(op3, op4), op5), self.ast_ctxt.bvfalse()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVG operation");

    //         /* Spread taint and condition flag */
    //         if ((op3.evaluate().is_zero() == op4.evaluate().is_zero()) && op5.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // // // expr.isTainted |= self.taintEngine.isTainted(sf) || self.taintEngine.isTainted(of) || self.taintEngine.isTainted(zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovge_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  sf  = Operand::Register(Register::SF);
    //         let  of  = Operand::Register(Register::OF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, of);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, op4), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVGE operation");

    //         /* Spread taint and condition flag */
    //         if (op3.evaluate().is_zero() == op4.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // // expr.isTainted |= self.taintEngine.isTainted(sf) || self.taintEngine.isTainted(of);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovl_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  sf  = Operand::Register(Register::SF);
    //         let  of  = Operand::Register(Register::OF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, of);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvxor(op3, op4), self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVL operation");

    //         /* Spread taint and condition flag */
    //         if (op3.evaluate().is_zero() != op4.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // // expr.isTainted |= self.taintEngine.isTainted(sf) || self.taintEngine.isTainted(of);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovle_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  sf  = Operand::Register(Register::SF);
    //         let  of  = Operand::Register(Register::OF);
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvor(self.ast_ctxt.bvxor(op3, op4), op5), self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVBE operation");

    //         /* Spread taint and condition flag */
    //         if ((op3.evaluate().is_zero() != op4.evaluate().is_zero()) || !op5.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // // // expr.isTainted |= self.taintEngine.isTainted(sf) || self.taintEngine.isTainted(of) || self.taintEngine.isTainted(zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovne_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVNE operation");

    //         /* Spread taint and condition flag */
    //         if (op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovno_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  of  = Operand::Register(Register::OF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, of);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVNO operation");

    //         /* Spread taint and condition flag */
    //         if (op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(of);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovnp_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  pf  = Operand::Register(Register::PF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, pf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVNP operation");

    //         /* Spread taint and condition flag */
    //         if (op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(pf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovns_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  sf  = Operand::Register(Register::SF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, sf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVNS operation");

    //         /* Spread taint and condition flag */
    //         if (op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(sf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovo_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  of  = Operand::Register(Register::OF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, of);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVO operation");

    //         /* Spread taint and condition flag */
    //         if (!op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(of);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovp_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  pf  = Operand::Register(Register::PF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, pf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVP operation");

    //         /* Spread taint and condition flag */
    //         if (!op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(pf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmovs_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let  sf  = Operand::Register(Register::SF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, sf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op3, self.ast_ctxt.bvtrue()), op2, op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CMOVS operation");

    //         /* Spread taint and condition flag */
    //         if (!op3.evaluate().is_zero()) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //           inst.setConditionTaken(true);
    //         }
    //         else {
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, dst);
    //         }

    //         // expr.isTainted |= self.taintEngine.isTainted(sf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmp_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.sx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvsub(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicVolatileExpression(inst, node, "CMP operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr, dst, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr, dst, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr, dst, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr, dst, ); // todo: vol = true
    //         self.sf_s(inst, expr, dst, ); // todo: vol = true
    //         self.zf_s(inst, expr, dst, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmpsb_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index1 = Operand::Register(Register::SI.full_register());
    //         let  index2 = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* If the REP prefix is defined, convert REP into REPE */
    //         if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP){
    //           inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);}

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index1);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, index2);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvsub(op1, op2);
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op5, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::BYTE, index1.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::BYTE, index1.get_bit_size()))
    //                      );
    //         let node3 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op5, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op4, self.ast_ctxt.bv(ByteSizes::BYTE, index2.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op4, self.ast_ctxt.bv(ByteSizes::BYTE, index2.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "CMPSB operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index1, index1);
    //         // expr3.isTainted = self.taintEngine.taintUnion(index2, index2);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.sf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.zf_s(inst, expr1, dst, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmpsd_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index1 = Operand::Register(Register::SI.full_register());
    //         let  index2 = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* If the REP prefix is defined, convert REP into REPE */
    //         if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP){
    //           inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);}

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index1);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, index2);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvsub(op1, op2);
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op5, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::DWORD, index1.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::DWORD, index1.get_bit_size()))
    //                      );
    //         let node3 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op5, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op4, self.ast_ctxt.bv(ByteSizes::DWORD, index2.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op4, self.ast_ctxt.bv(ByteSizes::DWORD, index2.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "CMPSD operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index1, index1);
    //         // expr3.isTainted = self.taintEngine.taintUnion(index2, index2);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.sf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.zf_s(inst, expr1, dst, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmpsq_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index1 = Operand::Register(Register::SI.full_register());
    //         let  index2 = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* If the REP prefix is defined, convert REP into REPE */
    //         if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP){
    //           inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);}

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index1);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, index2);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvsub(op1, op2);
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op5, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::QWORD, index1.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::QWORD, index1.get_bit_size()))
    //                      );
    //         let node3 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op5, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op4, self.ast_ctxt.bv(ByteSizes::QWORD, index2.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op4, self.ast_ctxt.bv(ByteSizes::QWORD, index2.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "CMPSQ operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index1, index1);
    //         // expr3.isTainted = self.taintEngine.taintUnion(index2, index2);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.sf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.zf_s(inst, expr1, dst, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmpsw_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index1 = Operand::Register(Register::SI.full_register());
    //         let  index2 = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* If the REP prefix is defined, convert REP into REPE */
    //         if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP){
    //           inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);}

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index1);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, index2);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvsub(op1, op2);
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op5, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::WORD, index1.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::WORD, index1.get_bit_size()))
    //                      );
    //         let node3 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op5, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op4, self.ast_ctxt.bv(ByteSizes::WORD, index2.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op4, self.ast_ctxt.bv(ByteSizes::WORD, index2.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "CMPSW operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index1, "Index (SI) operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, index2, "Index (DI) operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index1, index1);
    //         // expr3.isTainted = self.taintEngine.taintUnion(index2, index2);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.sf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.zf_s(inst, expr1, dst, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmpxchg_s(&mut self, inst: x86Instruction) {
    //         let src1  = inst.operands[0];
    //         let src2  = inst.operands[1];

    //         /* Create the tempory accumulator */
    //         triton::arch::OperandWrapper accumulator(Register::AL);
    //         triton::arch::OperandWrapper accumulatorp(Register::AL.full_register());

    //         switch (src1.getSize()) {
    //           case ByteSizes::WORD:
    //             accumulator.setRegister(arch::Register(Register::AX));
    //             break;
    //           case ByteSizes::DWORD:
    //             accumulator.setRegister(arch::Register(Register::EAX));
    //             break;
    //           case ByteSizes::QWORD:
    //             accumulator.setRegister(arch::Register(Register::RAX));
    //             break;
    //         }

    //         /* Create symbolic operands */
    //         let op1  = self.symbolicEngine.getOperandAst(inst, accumulator);
    //         let op2  = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3  = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op1p = self.symbolicEngine.getOperandAst(accumulatorp);
    //         let op2p = self.symbolicEngine.getRegisterAst(if src1.getType() == triton::arch::OP_REG { Register(self.architecture.getParentRegister(src1.getRegister())) } else { accumulatorp.getRegister() });
    //         let op3p = self.symbolicEngine.getRegisterAst(if src1.getType() == triton::arch::OP_REG { Register(self.architecture.getParentRegister(src2.getRegister())) } else { accumulatorp.getRegister() });

    //         /* Create the semantics */
    //         let nodeq  = self.ast_ctxt.equal(op1, op2);
    //         let node1  = self.ast_ctxt.bvsub(op1, op2);
    //         let node2  = self.ast_ctxt.ite(nodeq, op3, op2);
    //         let node3  = self.ast_ctxt.ite(nodeq, op1, op2);
    //         let node2p = self.ast_ctxt.ite(nodeq, op3p, op2p);
    //         let node3p = self.ast_ctxt.ite(nodeq, op1p, op2p);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "CMP operation");
    //         let expr2 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node2, "Temporary operation");
    //         let expr3 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node2p, "Temporary operation");
    //         let expr4 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node3, "Temporary operation");
    //         let expr5 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node3p, "Temporary operation");

    //         triton::engines::symbolic::SharedSymbolicExpression expr6 = nullptr;
    //         triton::engines::symbolic::SharedSymbolicExpression expr7 = nullptr;

    //         /* Destination */
    //         if (nodeq.evaluate() == false && src1.getType() == triton::arch::OP_REG) {
    //           const let src1p  = self.architecture.getParentRegister(src1.getRegister());
    //           expr6 = self.symbolicEngine.createSymbolicRegisterExpression(inst, node2p, src1p, "XCHG operation");
    //         } else
    //           expr6 = self.symbolicEngine.createSymbolicExpression(inst, node2, src1, "XCHG operation");

    //         /* Accumulator */
    //         if (nodeq.evaluate() == true){
    //           expr7 = self.symbolicEngine.createSymbolicExpression(inst, node3p, accumulatorp, "XCHG operation");
    //         }else{
    //           expr7 = self.symbolicEngine.createSymbolicExpression(inst, node3, accumulator, "XCHG operation");
    // }
    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(accumulator) | self.taintEngine.isTainted(src1);
    //         expr2.isTainted = expr1.isTainted;
    //         expr3.isTainted = expr1.isTainted;
    //         expr4.isTainted = expr1.isTainted;
    //         expr5.isTainted = expr1.isTainted;
    //         // expr6.isTainted = self.taintEngine.taintAssignment(src1, src2);
    //         // expr7.isTainted = self.taintEngine.taintAssignment(accumulator, src1);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, accumulator, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr1, accumulator, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr1, accumulator, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr1, accumulator, ); // todo: vol = true
    //         self.sf_s(inst, expr1, accumulator, ); // todo: vol = true
    //         self.zf_s(inst, expr1, accumulator, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmpxchg16b_s(&mut self, inst: x86Instruction) {
    //         let src1 = inst.operands[0];
    //         let  src2 = Operand::Register(Register::RDX);
    //         let  src3 = Operand::Register(Register::RAX);
    //         let  src4 = Operand::Register(Register::RCX);
    //         let  src5 = Operand::Register(Register::RBX);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src3);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, src4);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, src5);

    //         /* Create the semantics */
    //         /* CMP8B */
    //         let node1 = self.ast_ctxt.bvsub(self.ast_ctxt.concat(op2, op3), op1);
    //         /* Destination */
    //         let node2 = self.ast_ctxt.ite(self.ast_ctxt.equal(node1, self.ast_ctxt.bv(0, BitSizes::DQWORD)), self.ast_ctxt.concat(op4, op5), op1);
    //         /* EDX:EAX */
    //         let node3 = self.ast_ctxt.ite(self.ast_ctxt.equal(node1, self.ast_ctxt.bv(0, BitSizes::DQWORD)), self.ast_ctxt.concat(op2, op3), op1);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "CMP operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, src1, "XCHG16B memory operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract(127, 64, node3), src2, "XCHG16B RDX operation");
    //         let expr4 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract(63, 0, node3), src3, "XCHG16B RAX operation");

    //         /* Spread taint */
    //         // // // expr1.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2) | self.taintEngine.isTainted(src3);
    //         // // // expr2.isTainted = self.taintEngine.setTaint(src1, self.taintEngine.isTainted(src2) | self.taintEngine.isTainted(src3));
    //         // expr3.isTainted = self.taintEngine.taintAssignment(src2, src1);
    //         // expr4.isTainted = self.taintEngine.taintAssignment(src3, src1);

    //         /* Update symbolic flags */
    //         self.zf_s(inst, expr1, src1); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cmpxchg8b_s(&mut self, inst: x86Instruction) {
    //         let src1  = inst.operands[0];
    //         let  src2  = Operand::Register(Register::EDX);
    //         let  src3  = Operand::Register(Register::EAX);
    //         let  src4  = Operand::Register(Register::ECX);
    //         let  src5  = Operand::Register(Register::EBX);
    //         let  src2p = Operand::Register(Register::EDX.full_register());
    //         let  src3p = Operand::Register(Register::EAX.full_register());

    //         /* Create symbolic operands */
    //         let op1  = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2  = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3  = self.symbolicEngine.getOperandAst(inst, src3);
    //         let op4  = self.symbolicEngine.getOperandAst(inst, src4);
    //         let op5  = self.symbolicEngine.getOperandAst(inst, src5);
    //         let op2p = self.symbolicEngine.getOperandAst(inst, src2p);
    //         let op3p = self.symbolicEngine.getOperandAst(inst, src3p);

    //         /* Create the semantics */
    //         /* CMP8B */
    //         let node1 = self.ast_ctxt.bvsub(self.ast_ctxt.concat(op2, op3), op1);
    //         /* Destination */
    //         let node2 = self.ast_ctxt.ite(self.ast_ctxt.equal(node1, self.ast_ctxt.bv(0, BitSizes::QWORD)), self.ast_ctxt.concat(op4, op5), op1);
    //         /* EDX:EAX */
    //         let node3  = self.ast_ctxt.ite(self.ast_ctxt.equal(node1, self.ast_ctxt.bv(0, BitSizes::QWORD)), self.ast_ctxt.concat(op2, op3), op1);
    //         let node3p = self.ast_ctxt.ite(
    //                         self.ast_ctxt.equal(
    //                           node1,
    //                           self.ast_ctxt.bv(0, BitSizes::QWORD)),
    //                           self.ast_ctxt.concat(op2p, op3p),
    //                           self.ast_ctxt.zx(src2p.get_bit_size() + src3p.get_bit_size() - src1.get_bit_size(), op1)
    //                       );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "CMP operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, src1, "XCHG8B memory operation");
    //         let expr3 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node3, "Temporary operation");
    //         let expr4 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node3p, "Temporary operation");

    //         triton::engines::symbolic::SharedSymbolicExpression expr5;
    //         triton::engines::symbolic::SharedSymbolicExpression expr6;

    //         /* EDX */
    //         if (node1.evaluate() == 0){
    //           expr5 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract((src2p.get_bit_size() * 2 - 1), src2p.get_bit_size(), node3p), src2p, "XCHG8B EDX operation");
    //         }else{
    //           expr5 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract(63, 32, node3), src2, "XCHG8B EDX operation");
    // }
    //         /* EAX */
    //         if (node1.evaluate() == 0){
    //           expr6 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract(src2p.get_bit_size() - 1, 0, node3p), src3p, "XCHG8B EAX operation");
    //         }else{
    //           expr6 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract(31, 0, node3), src3, "XCHG8B EAX operation");
    // }
    //         /* Spread taint */
    //         // // // expr1.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2) | self.taintEngine.isTainted(src3);
    //         // // // expr2.isTainted = self.taintEngine.setTaint(src1, self.taintEngine.isTainted(src2) | self.taintEngine.isTainted(src3));
    //         // // // expr3.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2) | self.taintEngine.isTainted(src3);
    //         // // // expr4.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2) | self.taintEngine.isTainted(src3);
    //         // expr5.isTainted = self.taintEngine.taintAssignment(src2, src1);
    //         // expr6.isTainted = self.taintEngine.taintAssignment(src3, src1);

    //         /* Update symbolic flags */
    //         self.zf_s(inst, expr1, src1, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cpuid_s(&mut self, inst: x86Instruction) {
    //         let src  = Operand::Register(Register::AX.full_register());
    //         let dst1 = Operand::Register(Register::AX.full_register());
    //         let dst2 = Operand::Register(Register::BX.full_register());
    //         let dst3 = Operand::Register(Register::CX.full_register());
    //         let dst4 = Operand::Register(Register::DX.full_register());

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node1: Instruction;
    //         let mut node2: Instruction;
    //         let mut node3: Instruction;
    //         let mut node4: Instruction;

    //         /* In this case, we concretize the AX option */
    //         match op1.evaluate() as u32 {
    //           0 => {
    //             node1 = self.ast_ctxt.bv(0x0000000d, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x756e6547, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x6c65746e, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x49656e69, dst4.get_bit_size());
    //           }
    //           1 => {
    //             node1 = self.ast_ctxt.bv(0x000306a9, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x02100800, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x7fbae3ff, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0xbfebfbff, dst4.get_bit_size());
    //           }
    //           2 => {
    //             node1 = self.ast_ctxt.bv(0x76035a01, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00f0b2ff, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000000, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00ca0000, dst4.get_bit_size());
    //           }
    //           3 => {
    //             node1 = self.ast_ctxt.bv(0x00000000, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000000, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000000, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00000000, dst4.get_bit_size());
    //           }
    //           4 => {
    //             node1 = self.ast_ctxt.bv(0x1c004121, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x01c0003f, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x0000003f, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00000000, dst4.get_bit_size());
    //           }
    //           5 => {
    //             node1 = self.ast_ctxt.bv(0x00000040, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000040, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000003, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00021120, dst4.get_bit_size());
    //           }
    //           0x80000000 => {
    //             node1 = self.ast_ctxt.bv(0x80000008, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000000, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000000, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00000000, dst4.get_bit_size());
    //           }
    //           0x80000001 => {
    //             node1 = self.ast_ctxt.bv(0x00000000, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000000, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000001, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x28100800, dst4.get_bit_size());
    //           }
    //           0x80000002 => {
    //             node1 = self.ast_ctxt.bv(0x20202020, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x49202020, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x6c65746e, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x20295228, dst4.get_bit_size());
    //           }
    //           0x80000003 => {
    //             node1 = self.ast_ctxt.bv(0x65726f43, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x294d5428, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x2d376920, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x30323533, dst4.get_bit_size());
    //           }
    //           0x80000004 => {
    //             node1 = self.ast_ctxt.bv(0x5043204d, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x20402055, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x30392e32, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x007a4847, dst4.get_bit_size());
    //           }
    //           0x80000005 => {
    //             node1 = self.ast_ctxt.bv(0x00000000, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000000, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000000, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00000000, dst4.get_bit_size());
    //           }
    //           0x80000006 => {
    //             node1 = self.ast_ctxt.bv(0x00000000, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000000, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x01006040, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00000000, dst4.get_bit_size());
    //           }
    //           0x80000007 => {
    //             node1 = self.ast_ctxt.bv(0x00000000, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000000, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000000, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00000100, dst4.get_bit_size());
    //           }
    //           0x80000008 => {
    //             node1 = self.ast_ctxt.bv(0x00003024, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000000, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000000, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00000000, dst4.get_bit_size());
    //           }
    //           _ => {
    //             node1 = self.ast_ctxt.bv(0x00000007, dst1.get_bit_size());
    //             node2 = self.ast_ctxt.bv(0x00000340, dst2.get_bit_size());
    //             node3 = self.ast_ctxt.bv(0x00000340, dst3.get_bit_size());
    //             node4 = self.ast_ctxt.bv(0x00000000, dst4.get_bit_size());
    //             }
    //         }

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst1, "CPUID AX operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2, "CPUID BX operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, dst3, "CPUID CX operation");
    //         let expr4 = self.symbolicEngine.createSymbolicExpression(inst, node4, dst4, "CPUID DX operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.setTaintRegister(Register::AX.full_register(), false);
    //         // expr2.isTainted = self.taintEngine.setTaintRegister(Register::BX.full_register(), false);
    //         // expr3.isTainted = self.taintEngine.setTaintRegister(Register::CX.full_register(), false);
    //         // expr4.isTainted = self.taintEngine.setTaintRegister(Register::DX.full_register(), false);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cqo_s(&mut self, inst: x86Instruction) {
    //         let dst = Operand::Register(Register::RDX);
    //         let src = Operand::Register(Register::RAX);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics - TMP = 128 bitvec (RDX:RAX) */
    //         let node1 = self.ast_ctxt.sx(BitSizes::QWORD, op1);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "Temporary variable");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.isRegisterTainted(Register::RAX);

    //         /* Create the semantics - RDX = TMP[127...64] */
    //         let node2 = self.ast_ctxt.extract(BitSizes::DQWORD-1, BitSizes::QWORD, self.ast_ctxt.reference(expr1));

    //         /* Create symbolic expression */
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst, "CQO operation");

    //         /* Spread taint */
    //         // expr2.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cwd_s(&mut self, inst: x86Instruction) {
    //         let dst = Operand::Register(Register::DX);
    //         let src = Operand::Register(Register::AX);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics - TMP = 32 bitvec (DX:AX) */
    //         let node1 = self.ast_ctxt.sx(BitSizes::WORD, op1);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "Temporary variable");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.isRegisterTainted(Register::AX);

    //         /* Create the semantics - DX = TMP[31...16] */
    //         let node2 = self.ast_ctxt.extract(BitSizes::DWORD-1, BitSizes::WORD, self.ast_ctxt.reference(expr1));

    //         /* Create symbolic expression */
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst, "CWD operation");

    //         /* Spread taint */
    //         // expr2.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn cwde_s(&mut self, inst: x86Instruction) {
    //         let dst = Operand::Register(Register::EAX);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(BitSizes::WORD-1, 0, op1));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "CWDE operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn dec_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.bv(1, dst.get_bit_size());

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvsub(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "DEC operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr, dst, op1, op2);
    //         self.ofSub_s(inst, expr, dst, op1, op2);
    //         self.pf_s(inst, expr, dst);
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn div_s(&mut self, inst: x86Instruction) {
    //         let src = inst.operands[0];

    //         /* Create symbolic operands */
    //         let divisor = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         match src.getSize() {

    //           ByteSizes::BYTE => {
    //             /* AX */
    //             let ax = Operand::Register(Register::AX);
    //             let dividend = self.symbolicEngine.getOperandAst(inst, ax);
    //             /* res = AX / Source */
    //             let result = self.ast_ctxt.bvudiv(dividend, self.ast_ctxt.zx(BitSizes::BYTE, divisor));
    //             /* mod_ = AX % Source */
    //             let mod_ = self.ast_ctxt.bvurem(dividend, self.ast_ctxt.zx(BitSizes::BYTE, divisor));
    //             /* AH = mod_ */
    //             /* AL = res */
    //             let node = self.ast_ctxt.concat(
    //                           self.ast_ctxt.extract((BitSizes::BYTE - 1), 0, mod_),   /* AH = mod_ */
    //                           self.ast_ctxt.extract((BitSizes::BYTE - 1), 0, result) /* AL = res */
    //                         );
    //             /* Create symbolic expression */
    //             let expr = self.symbolicEngine.createSymbolicExpression(inst, node, ax, "DIV operation");
    //             /* Apply the taint */
    //             // expr.isTainted = self.taintEngine.taintUnion(ax, src);
    //             /* Divide error */
    //             if (result.evaluate() > 0xff) {
    //             //   self.exception = triton::arch::FAULT_DE;
    //               return;
    //             }
    //           }

    //           ByteSizes::WORD => {
    //             /* DX:AX */
    //             let dx = Operand::Register(Register::DX);
    //             let ax = Operand::Register(Register::AX);
    //             let dividend = self.ast_ctxt.concat(self.symbolicEngine.getOperandAst(inst, dx), self.symbolicEngine.getOperandAst(inst, ax));
    //             /* res = DX:AX / Source */
    //             let temp = self.ast_ctxt.bvudiv(dividend, self.ast_ctxt.zx(BitSizes::WORD, divisor));
    //             let result = self.ast_ctxt.extract((BitSizes::WORD - 1), 0, temp);
    //             /* mod_ = DX:AX % Source */
    //             let mod_ = self.ast_ctxt.extract((BitSizes::WORD - 1), 0, self.ast_ctxt.bvurem(dividend, self.ast_ctxt.zx(BitSizes::WORD, divisor)));
    //             /* Create the symbolic expression for AX */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, result, ax, "DIV operation");
    //             /* Apply the taint for AX */
    //             // expr1.isTainted = self.taintEngine.taintUnion(ax, src);
    //             /* Create the symbolic expression for DX */
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, mod_, dx, "DIV operation");
    //             /* Apply the taint for DX */
    //             // expr2.isTainted = self.taintEngine.taintUnion(dx, src);
    //             /* Divide error */
    //             if (temp.evaluate() > 0xffff) {
    //             //   self.exception = triton::arch::FAULT_DE;
    //               return;
    //             }
    //           }

    //           ByteSizes::DWORD => {
    //             /* EDX:EAX */
    //             let edx = Operand::Register(Register::EDX);
    //             let eax = Operand::Register(Register::EAX);
    //             let dividend = self.ast_ctxt.concat(self.symbolicEngine.getOperandAst(inst, edx), self.symbolicEngine.getOperandAst(inst, eax));
    //             /* res = EDX:EAX / Source */
    //             let temp = self.ast_ctxt.bvudiv(dividend, self.ast_ctxt.zx(BitSizes::DWORD, divisor));
    //             let result = self.ast_ctxt.extract((BitSizes::DWORD - 1), 0, temp);
    //             /* mod_ = EDX:EAX % Source */
    //             let mod_ = self.ast_ctxt.extract((BitSizes::DWORD - 1), 0, self.ast_ctxt.bvurem(dividend, self.ast_ctxt.zx(BitSizes::DWORD, divisor)));
    //             /* Create the symbolic expression for EAX */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, result, eax, "DIV operation");
    //             /* Apply the taint for EAX */
    //             // expr1.isTainted = self.taintEngine.taintUnion(eax, src);
    //             /* Create the symbolic expression for EDX */
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, mod_, edx, "DIV operation");
    //             /* Apply the taint for EDX */
    //             // expr2.isTainted = self.taintEngine.taintUnion(edx, src);
    //             /* Divide error */
    //             if (temp.evaluate() > 0xffffffff) {
    //             //   self.exception = triton::arch::FAULT_DE;
    //               return;
    //             }
    //           }

    //           ByteSizes::QWORD => {
    //             /* RDX:RAX */
    //             let rdx = Operand::Register(Register::RDX);
    //             let rax = Operand::Register(Register::RAX);
    //             let dividend = self.ast_ctxt.concat(self.symbolicEngine.getOperandAst(inst, rdx), self.symbolicEngine.getOperandAst(inst, rax));
    //             /* res = RDX:RAX / Source */
    //             let temp = self.ast_ctxt.bvudiv(dividend, self.ast_ctxt.zx(BitSizes::QWORD, divisor));
    //             let result = self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, temp);
    //             /* mod_ = RDX:RAX % Source */
    //             let mod_ = self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, self.ast_ctxt.bvurem(dividend, self.ast_ctxt.zx(BitSizes::QWORD, divisor)));
    //             /* Create the symbolic expression for RAX */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, result, rax, "DIV operation");
    //             /* Apply the taint for EAX */
    //             // expr1.isTainted = self.taintEngine.taintUnion(rax, src);
    //             /* Create the symbolic expression for RDX */
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, mod_, rdx, "DIV operation");
    //             /* Apply the taint for EDX */
    //             // expr2.isTainted = self.taintEngine.taintUnion(rdx, src);
    //             /* Divide error */
    //             if (temp.evaluate() > 0xffffffffffffffff) {
    //             //   self.exception = triton::arch::FAULT_DE;
    //               return;
    //             }
    //           }

    //         }

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::CF);
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);
    //         self.undefined_s(inst, Register::ZF);

    //         /* Return an exception if the divisor is zero */
    //         if (divisor.evaluate() == 0) {
    //         //   self.exception = triton::arch::FAULT_DE;
    //           return;
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn endbr32_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn endbr64_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn extractps_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut node = self.ast_ctxt.extract(BitSizes::DWORD-1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bvmul(
    //                           self.ast_ctxt.zx(126, self.ast_ctxt.extract(1, 0, op3)),
    //                           self.ast_ctxt.bv(BitSizes::DWORD, BitSizes::DQWORD)
    //                         )
    //                       )
    //                     );

    //         match dst.get_bit_size() {
    //           BitSizes::DWORD => {}
    //           BitSizes::QWORD => {
    //               node = self.ast_ctxt.zx(BitSizes::DWORD, node);
    //           }
    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::extractps_s(): Invalid destination operand.");"#)
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "EXTRACTPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn fxrstor_s(&mut self, inst: x86Instruction) {
    //         /* Fetch the current architecture */
    //         let arch = self.architecture.getArchitecture();

    //         /* Determine if we are executing in 64 bit mode */
    //         let is64bits = arch == triton::arch::architecture_e::ARCH_X86_64;

    //         /* Fetch the memory operand */
    //         let dst = inst.operands[0];
    //         let mem = dst.getMemory();
    //         let m512byte = mem.getAddress();

    //         /* Check if the address is on a 16-byte boundary */
    //         if (m512byte & 0xF) {
    //         //   self.exception = triton::arch::FAULT_GP;
    //           return;
    //         }

    //         /* Fetch the FPU, STX, SSE, EFER and CS implicit operands */
    //         let fcw        = Operand::Register(Register::FCW);
    //         let fsw        = Operand::Register(Register::FSW);
    //         let ftw        = Operand::Register(Register::FTW);
    //         let fop        = Operand::Register(Register::FOP);
    //         let fip        = Operand::Register(Register::FIP);
    //         let fcs        = Operand::Register(Register::FCS);
    //         let fdp        = Operand::Register(Register::FDP);
    //         let fds        = Operand::Register(Register::FDS);
    //         let mxcsr      = Operand::Register(Register::MXCSR);
    //         let mxcsr_mask = Operand::Register(Register::MXCSR_MASK);
    //         let st0        = Operand::Register(Register::ST0);
    //         let st1        = Operand::Register(Register::ST1);
    //         let st2        = Operand::Register(Register::ST2);
    //         let st3        = Operand::Register(Register::ST3);
    //         let st4        = Operand::Register(Register::ST4);
    //         let st5        = Operand::Register(Register::ST5);
    //         let st6        = Operand::Register(Register::ST6);
    //         let st7        = Operand::Register(Register::ST7);
    //         let xmm0       = Operand::Register(Register::XMM0);
    //         let xmm1       = Operand::Register(Register::XMM1);
    //         let xmm2       = Operand::Register(Register::XMM2);
    //         let xmm3       = Operand::Register(Register::XMM3);
    //         let xmm4       = Operand::Register(Register::XMM4);
    //         let xmm5       = Operand::Register(Register::XMM5);
    //         let xmm6       = Operand::Register(Register::XMM6);
    //         let xmm7       = Operand::Register(Register::XMM7);
    //         let ffxsr      = Operand::Register(Register::EFER_FFXSR);
    //         let cs         = Operand::Register(Register::CS);

    //         /* Fetch the implicit memory slots for the 'Non-64-bit Mode Layout' */
    //         let fcw_addr         = Operand::Memory(MemoryAccess::new(m512byte + 0, fcw.getSize()));
    //         let fsw_addr         = Operand::Memory(MemoryAccess::new(m512byte + 2, fsw.getSize()));
    //         let ftw_addr         = Operand::Memory(MemoryAccess::new(m512byte + 4, ftw.getSize() / 2));
    //         let fop_addr         = Operand::Memory(MemoryAccess::new(m512byte + 6, fop.getSize()));
    //         let fip_addr         = Operand::Memory(MemoryAccess::new(m512byte + 8, fip.getSize() / 2));
    //         let fcs_addr         = Operand::Memory(MemoryAccess::new(m512byte + 12, fcs.getSize()));
    //         let fdp_addr         = Operand::Memory(MemoryAccess::new(m512byte + 16, fdp.getSize() / 2));
    //         let fds_addr         = Operand::Memory(MemoryAccess::new(m512byte + 20, fds.getSize()));
    //         let mxcsr_addr       = Operand::Memory(MemoryAccess::new(m512byte + 24, mxcsr.getSize()));
    //         let mxcsr_mask_addr  = Operand::Memory(MemoryAccess::new(m512byte + 28, mxcsr_mask.getSize()));
    //         let st0_addr         = Operand::Memory(MemoryAccess::new(m512byte + 32,  st0.getSize()));
    //         let st1_addr         = Operand::Memory(MemoryAccess::new(m512byte + 48,  st1.getSize()));
    //         let st2_addr         = Operand::Memory(MemoryAccess::new(m512byte + 64,  st2.getSize()));
    //         let st3_addr         = Operand::Memory(MemoryAccess::new(m512byte + 80,  st3.getSize()));
    //         let st4_addr         = Operand::Memory(MemoryAccess::new(m512byte + 96,  st4.getSize()));
    //         let st5_addr         = Operand::Memory(MemoryAccess::new(m512byte + 112, st5.getSize()));
    //         let st6_addr         = Operand::Memory(MemoryAccess::new(m512byte + 128, st6.getSize()));
    //         let st7_addr         = Operand::Memory(MemoryAccess::new(m512byte + 144, st7.getSize()));
    //         let xmm0_addr        = Operand::Memory(MemoryAccess::new(m512byte + 160, xmm0.getSize()));
    //         let xmm1_addr        = Operand::Memory(MemoryAccess::new(m512byte + 176, xmm1.getSize()));
    //         let xmm2_addr        = Operand::Memory(MemoryAccess::new(m512byte + 192, xmm2.getSize()));
    //         let xmm3_addr        = Operand::Memory(MemoryAccess::new(m512byte + 208, xmm3.getSize()));
    //         let xmm4_addr        = Operand::Memory(MemoryAccess::new(m512byte + 224, xmm4.getSize()));
    //         let xmm5_addr        = Operand::Memory(MemoryAccess::new(m512byte + 240, xmm5.getSize()));
    //         let xmm6_addr        = Operand::Memory(MemoryAccess::new(m512byte + 256, xmm6.getSize()));
    //         let xmm7_addr        = Operand::Memory(MemoryAccess::new(m512byte + 272, xmm7.getSize()));

    //         /* Create the symbolic operands */
    //         let fcw_ast          = self.symbolicEngine.getOperandAst(inst, fcw_addr);
    //         let fsw_ast          = self.symbolicEngine.getOperandAst(inst, fsw_addr);
    //         let ftw_ast          = self.symbolicEngine.getOperandAst(inst, ftw_addr);
    //         let fop_ast          = self.symbolicEngine.getOperandAst(inst, fop_addr);
    //         let fip_ast          = self.ast_ctxt.zx(BitSizes::DWORD, self.symbolicEngine.getOperandAst(inst, fip_addr));
    //         let fcs_ast          = self.symbolicEngine.getOperandAst(inst, fcs_addr);
    //         let fdp_ast          = self.ast_ctxt.zx(BitSizes::DWORD, self.symbolicEngine.getOperandAst(inst, fdp_addr));
    //         let fds_ast          = self.symbolicEngine.getOperandAst(inst, fds_addr);
    //         let mxcsr_ast        = self.symbolicEngine.getOperandAst(inst, mxcsr_addr);
    //         let mxcsr_mask_ast   = self.symbolicEngine.getOperandAst(inst, mxcsr_mask_addr);
    //         let st0_ast          = self.symbolicEngine.getOperandAst(inst, st0_addr);
    //         let st1_ast          = self.symbolicEngine.getOperandAst(inst, st1_addr);
    //         let st2_ast          = self.symbolicEngine.getOperandAst(inst, st2_addr);
    //         let st3_ast          = self.symbolicEngine.getOperandAst(inst, st3_addr);
    //         let st4_ast          = self.symbolicEngine.getOperandAst(inst, st4_addr);
    //         let st5_ast          = self.symbolicEngine.getOperandAst(inst, st5_addr);
    //         let st6_ast          = self.symbolicEngine.getOperandAst(inst, st6_addr);
    //         let st7_ast          = self.symbolicEngine.getOperandAst(inst, st7_addr);
    //         let xmm0_ast         = self.symbolicEngine.getOperandAst(inst, xmm0_addr);
    //         let xmm1_ast         = self.symbolicEngine.getOperandAst(inst, xmm1_addr);
    //         let xmm2_ast         = self.symbolicEngine.getOperandAst(inst, xmm2_addr);
    //         let xmm3_ast         = self.symbolicEngine.getOperandAst(inst, xmm3_addr);
    //         let xmm4_ast         = self.symbolicEngine.getOperandAst(inst, xmm4_addr);
    //         let xmm5_ast         = self.symbolicEngine.getOperandAst(inst, xmm5_addr);
    //         let xmm6_ast         = self.symbolicEngine.getOperandAst(inst, xmm6_addr);
    //         let xmm7_ast         = self.symbolicEngine.getOperandAst(inst, xmm7_addr);
    //         let ffxsr_ast        = self.symbolicEngine.getOperandAst(inst, ffxsr);
    //         let cs_ast           = self.symbolicEngine.getOperandAst(inst, cs);

    //         /* Fetch the original values for the XMM0-XMM7 registers */
    //         let xmm0_orig = self.symbolicEngine.getOperandAst(inst, xmm0);
    //         let xmm1_orig = self.symbolicEngine.getOperandAst(inst, xmm1);
    //         let xmm2_orig = self.symbolicEngine.getOperandAst(inst, xmm2);
    //         let xmm3_orig = self.symbolicEngine.getOperandAst(inst, xmm3);
    //         let xmm4_orig = self.symbolicEngine.getOperandAst(inst, xmm4);
    //         let xmm5_orig = self.symbolicEngine.getOperandAst(inst, xmm5);
    //         let xmm6_orig = self.symbolicEngine.getOperandAst(inst, xmm6);
    //         let xmm7_orig = self.symbolicEngine.getOperandAst(inst, xmm7);

    //         /* Check if we are running in CPL = 0 (ring 0) and if the FFXSR bit is set in EFER */
    //         let cpl     = self.ast_ctxt.equal(self.ast_ctxt.extract(1, 0, cs_ast), self.ast_ctxt.bv(0, 2));
    //         let ffx     = self.ast_ctxt.equal(ffxsr_ast, self.ast_ctxt.bv(1, 1));
    //         let b64     = self.ast_ctxt.equal(self.ast_ctxt.bv(is64bits, 1), self.ast_ctxt.bv(1, 1));
    //         let is_fast = self.ast_ctxt.land(self.ast_ctxt.land(cpl, ffx), b64);

    //         /* Apply the fast restore logic if needed */
    //         xmm0_ast = self.ast_ctxt.ite(is_fast, xmm0_orig, xmm0_ast);
    //         xmm1_ast = self.ast_ctxt.ite(is_fast, xmm1_orig, xmm1_ast);
    //         xmm2_ast = self.ast_ctxt.ite(is_fast, xmm2_orig, xmm2_ast);
    //         xmm3_ast = self.ast_ctxt.ite(is_fast, xmm3_orig, xmm3_ast);
    //         xmm4_ast = self.ast_ctxt.ite(is_fast, xmm4_orig, xmm4_ast);
    //         xmm5_ast = self.ast_ctxt.ite(is_fast, xmm5_orig, xmm5_ast);
    //         xmm6_ast = self.ast_ctxt.ite(is_fast, xmm6_orig, xmm6_ast);
    //         xmm7_ast = self.ast_ctxt.ite(is_fast, xmm7_orig, xmm7_ast);

    //         /* Fetch the abridged x87 FPU Tag Word Encoded Bits */
    //         let eb_1_0   = self.ast_ctxt.extract(0, 0, ftw_ast);
    //         let eb_3_2   = self.ast_ctxt.extract(1, 1, ftw_ast);
    //         let eb_5_4   = self.ast_ctxt.extract(2, 2, ftw_ast);
    //         let eb_7_6   = self.ast_ctxt.extract(3, 3, ftw_ast);
    //         let eb_9_8   = self.ast_ctxt.extract(4, 4, ftw_ast);
    //         let eb_11_10 = self.ast_ctxt.extract(5, 5, ftw_ast);
    //         let eb_13_12 = self.ast_ctxt.extract(6, 6, ftw_ast);
    //         let eb_15_14 = self.ast_ctxt.extract(7, 7, ftw_ast);

    //         /* Extract the fraction from the STX registers */
    //         let fraction_st0 = self.ast_ctxt.extract(62, 0, st0_ast);
    //         let fraction_st1 = self.ast_ctxt.extract(62, 0, st1_ast);
    //         let fraction_st2 = self.ast_ctxt.extract(62, 0, st2_ast);
    //         let fraction_st3 = self.ast_ctxt.extract(62, 0, st3_ast);
    //         let fraction_st4 = self.ast_ctxt.extract(62, 0, st4_ast);
    //         let fraction_st5 = self.ast_ctxt.extract(62, 0, st5_ast);
    //         let fraction_st6 = self.ast_ctxt.extract(62, 0, st6_ast);
    //         let fraction_st7 = self.ast_ctxt.extract(62, 0, st7_ast);

    //         /* Extract the integer bit from the STX registers */
    //         let integer_st0 = self.ast_ctxt.extract(63, 63, st0_ast);
    //         let integer_st1 = self.ast_ctxt.extract(63, 63, st1_ast);
    //         let integer_st2 = self.ast_ctxt.extract(63, 63, st2_ast);
    //         let integer_st3 = self.ast_ctxt.extract(63, 63, st3_ast);
    //         let integer_st4 = self.ast_ctxt.extract(63, 63, st4_ast);
    //         let integer_st5 = self.ast_ctxt.extract(63, 63, st5_ast);
    //         let integer_st6 = self.ast_ctxt.extract(63, 63, st6_ast);
    //         let integer_st7 = self.ast_ctxt.extract(63, 63, st7_ast);

    //         /* Extract the exponent from the STX registers */
    //         let exponent_st0 = self.ast_ctxt.extract(79, 64, st0_ast);
    //         let exponent_st1 = self.ast_ctxt.extract(79, 64, st1_ast);
    //         let exponent_st2 = self.ast_ctxt.extract(79, 64, st2_ast);
    //         let exponent_st3 = self.ast_ctxt.extract(79, 64, st3_ast);
    //         let exponent_st4 = self.ast_ctxt.extract(79, 64, st4_ast);
    //         let exponent_st5 = self.ast_ctxt.extract(79, 64, st5_ast);
    //         let exponent_st6 = self.ast_ctxt.extract(79, 64, st6_ast);
    //         let exponent_st7 = self.ast_ctxt.extract(79, 64, st7_ast);

    //         /* Exponent All Zeros */
    //         let ea0_st0 = self.ast_ctxt.equal(exponent_st0, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st1 = self.ast_ctxt.equal(exponent_st1, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st2 = self.ast_ctxt.equal(exponent_st2, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st3 = self.ast_ctxt.equal(exponent_st3, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st4 = self.ast_ctxt.equal(exponent_st4, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st5 = self.ast_ctxt.equal(exponent_st5, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st6 = self.ast_ctxt.equal(exponent_st6, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st7 = self.ast_ctxt.equal(exponent_st7, self.ast_ctxt.bv(0x0000, 16));

    //         /* Exponent All Ones */
    //         let ea1_st0 = self.ast_ctxt.equal(exponent_st0, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st1 = self.ast_ctxt.equal(exponent_st1, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st2 = self.ast_ctxt.equal(exponent_st2, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st3 = self.ast_ctxt.equal(exponent_st3, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st4 = self.ast_ctxt.equal(exponent_st4, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st5 = self.ast_ctxt.equal(exponent_st5, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st6 = self.ast_ctxt.equal(exponent_st6, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st7 = self.ast_ctxt.equal(exponent_st7, self.ast_ctxt.bv(0xFFFF, 16));

    //         /* Exponent Neither All Zeroes Or Ones */
    //         let ena01_st0 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st0, ea1_st0), self.ast_ctxt.bvfalse());
    //         let ena01_st1 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st1, ea1_st1), self.ast_ctxt.bvfalse());
    //         let ena01_st2 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st2, ea1_st2), self.ast_ctxt.bvfalse());
    //         let ena01_st3 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st3, ea1_st3), self.ast_ctxt.bvfalse());
    //         let ena01_st4 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st4, ea1_st4), self.ast_ctxt.bvfalse());
    //         let ena01_st5 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st5, ea1_st5), self.ast_ctxt.bvfalse());
    //         let ena01_st6 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st6, ea1_st6), self.ast_ctxt.bvfalse());
    //         let ena01_st7 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st7, ea1_st7), self.ast_ctxt.bvfalse());

    //         /* Integer Bit 0 */
    //         let ib0_st0 = self.ast_ctxt.equal(integer_st0, self.ast_ctxt.bv(0, 1));
    //         let ib0_st1 = self.ast_ctxt.equal(integer_st1, self.ast_ctxt.bv(0, 1));
    //         let ib0_st2 = self.ast_ctxt.equal(integer_st2, self.ast_ctxt.bv(0, 1));
    //         let ib0_st3 = self.ast_ctxt.equal(integer_st3, self.ast_ctxt.bv(0, 1));
    //         let ib0_st4 = self.ast_ctxt.equal(integer_st4, self.ast_ctxt.bv(0, 1));
    //         let ib0_st5 = self.ast_ctxt.equal(integer_st5, self.ast_ctxt.bv(0, 1));
    //         let ib0_st6 = self.ast_ctxt.equal(integer_st6, self.ast_ctxt.bv(0, 1));
    //         let ib0_st7 = self.ast_ctxt.equal(integer_st7, self.ast_ctxt.bv(0, 1));

    //         /* Fraction All Zeroes */
    //         let fa0_st0 = self.ast_ctxt.equal(fraction_st0, self.ast_ctxt.bv(0, 63));
    //         let fa0_st1 = self.ast_ctxt.equal(fraction_st1, self.ast_ctxt.bv(0, 63));
    //         let fa0_st2 = self.ast_ctxt.equal(fraction_st2, self.ast_ctxt.bv(0, 63));
    //         let fa0_st3 = self.ast_ctxt.equal(fraction_st3, self.ast_ctxt.bv(0, 63));
    //         let fa0_st4 = self.ast_ctxt.equal(fraction_st4, self.ast_ctxt.bv(0, 63));
    //         let fa0_st5 = self.ast_ctxt.equal(fraction_st5, self.ast_ctxt.bv(0, 63));
    //         let fa0_st6 = self.ast_ctxt.equal(fraction_st6, self.ast_ctxt.bv(0, 63));
    //         let fa0_st7 = self.ast_ctxt.equal(fraction_st7, self.ast_ctxt.bv(0, 63));

    //         /* Determine the x87 FPU Tag Word (Diagram at page 379 of the AMD Architecture Programmer's Manual, Volume 2: System Programming) */
    //         let db_1_0 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_1_0, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st0,
    //             self.ast_ctxt.ite(ib0_st0,
    //               self.ast_ctxt.ite(fa0_st0,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st0,
    //               self.ast_ctxt.ite(ib0_st0,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_3_2 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_3_2, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st1,
    //             self.ast_ctxt.ite(ib0_st1,
    //               self.ast_ctxt.ite(fa0_st1,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st1,
    //               self.ast_ctxt.ite(ib0_st1,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_5_4 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_5_4, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st2,
    //             self.ast_ctxt.ite(ib0_st2,
    //               self.ast_ctxt.ite(fa0_st2,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st2,
    //               self.ast_ctxt.ite(ib0_st2,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_7_6 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_7_6, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st3,
    //             self.ast_ctxt.ite(ib0_st3,
    //               self.ast_ctxt.ite(fa0_st3,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st3,
    //               self.ast_ctxt.ite(ib0_st3,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_9_8 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_9_8, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st4,
    //             self.ast_ctxt.ite(ib0_st4,
    //               self.ast_ctxt.ite(fa0_st4,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st4,
    //               self.ast_ctxt.ite(ib0_st4,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_11_10 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_11_10, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st5,
    //             self.ast_ctxt.ite(ib0_st5,
    //               self.ast_ctxt.ite(fa0_st5,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st5,
    //               self.ast_ctxt.ite(ib0_st5,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_13_12 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_13_12, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st6,
    //             self.ast_ctxt.ite(ib0_st6,
    //               self.ast_ctxt.ite(fa0_st6,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st6,
    //               self.ast_ctxt.ite(ib0_st6,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_15_14 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_15_14, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st7,
    //             self.ast_ctxt.ite(ib0_st7,
    //               self.ast_ctxt.ite(fa0_st7,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st7,
    //               self.ast_ctxt.ite(ib0_st7,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         /* Restore the x87 FPU Tag Word */
    //         let uftw_ast = self.ast_ctxt.concat(db_15_14,
    //           self.ast_ctxt.concat(db_13_12,
    //           self.ast_ctxt.concat(db_11_10,
    //           self.ast_ctxt.concat(db_9_8,
    //           self.ast_ctxt.concat(db_7_6,
    //           self.ast_ctxt.concat(db_5_4,
    //           self.ast_ctxt.concat(db_3_2, db_1_0)))))));

    //         /* Craft the symbolic expressions */
    //         let fcw_expr        = self.symbolicEngine.createSymbolicExpression(inst, fcw_ast, fcw, "FXRSTOR FCW operation");
    //         let fsw_expr        = self.symbolicEngine.createSymbolicExpression(inst, fsw_ast, fsw, "FXRSTOR FSW operation");
    //         let ftw_expr        = self.symbolicEngine.createSymbolicExpression(inst, uftw_ast, ftw, "FXRSTOR Updated FTW operation");
    //         let fop_expr        = self.symbolicEngine.createSymbolicExpression(inst, fop_ast, fop, "FXRSTOR FOP operation");
    //         let fip_expr        = self.symbolicEngine.createSymbolicExpression(inst, fip_ast, fip, "FXRSTOR FIP operation");
    //         let fcs_expr        = self.symbolicEngine.createSymbolicExpression(inst, fcs_ast, fcs, "FXRSTOR FCS operation");
    //         let fdp_expr        = self.symbolicEngine.createSymbolicExpression(inst, fdp_ast, fdp, "FXRSTOR FDP operation");
    //         let fds_expr        = self.symbolicEngine.createSymbolicExpression(inst, fds_ast, fds, "FXRSTOR FDS operation");
    //         let mxcsr_expr      = self.symbolicEngine.createSymbolicExpression(inst, mxcsr_ast, mxcsr, "FXRSTOR MXCSR operation");
    //         let mxcsr_mask_expr = self.symbolicEngine.createSymbolicExpression(inst, mxcsr_mask_ast, mxcsr_mask, "FXRSTOR MXCSR_MASK operation");
    //         let st0_expr        = self.symbolicEngine.createSymbolicExpression(inst, st0_ast, st0, "FXRSTOR ST0 operation");
    //         let st1_expr        = self.symbolicEngine.createSymbolicExpression(inst, st1_ast, st1, "FXRSTOR ST1 operation");
    //         let st2_expr        = self.symbolicEngine.createSymbolicExpression(inst, st2_ast, st2, "FXRSTOR ST2 operation");
    //         let st3_expr        = self.symbolicEngine.createSymbolicExpression(inst, st3_ast, st3, "FXRSTOR ST3 operation");
    //         let st4_expr        = self.symbolicEngine.createSymbolicExpression(inst, st4_ast, st4, "FXRSTOR ST4 operation");
    //         let st5_expr        = self.symbolicEngine.createSymbolicExpression(inst, st5_ast, st5, "FXRSTOR ST5 operation");
    //         let st6_expr        = self.symbolicEngine.createSymbolicExpression(inst, st6_ast, st6, "FXRSTOR ST6 operation");
    //         let st7_expr        = self.symbolicEngine.createSymbolicExpression(inst, st7_ast, st7, "FXRSTOR ST7 operation");
    //         let xmm0_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm0_ast, xmm0, "FXRSTOR XMM0 operation");
    //         let xmm1_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm1_ast, xmm1, "FXRSTOR XMM1 operation");
    //         let xmm2_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm2_ast, xmm2, "FXRSTOR XMM2 operation");
    //         let xmm3_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm3_ast, xmm3, "FXRSTOR XMM3 operation");
    //         let xmm4_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm4_ast, xmm4, "FXRSTOR XMM4 operation");
    //         let xmm5_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm5_ast, xmm5, "FXRSTOR XMM5 operation");
    //         let xmm6_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm6_ast, xmm6, "FXRSTOR XMM6 operation");
    //         let xmm7_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm7_ast, xmm7, "FXRSTOR XMM7 operation");

    //         /* Spread the taint */
    //         // fcw_expr.isTainted        = self.taintEngine.taintAssignment(fcw, fcw_addr);
    //         // fsw_expr.isTainted        = self.taintEngine.taintAssignment(fsw, fsw_addr);
    //         // ftw_expr.isTainted        = self.taintEngine.taintAssignment(ftw, ftw_addr);
    //         // fop_expr.isTainted        = self.taintEngine.taintAssignment(fop, fop_addr);
    //         // fip_expr.isTainted        = self.taintEngine.taintAssignment(fip, fip_addr);
    //         // fcs_expr.isTainted        = self.taintEngine.taintAssignment(fcs, fcs_addr);
    //         // fdp_expr.isTainted        = self.taintEngine.taintAssignment(fdp, fdp_addr);
    //         // fds_expr.isTainted        = self.taintEngine.taintAssignment(fds, fds_addr);
    //         // mxcsr_expr.isTainted      = self.taintEngine.taintAssignment(mxcsr, mxcsr_addr);
    //         // mxcsr_mask_expr.isTainted = self.taintEngine.taintAssignment(mxcsr_mask, mxcsr_mask_addr);
    //         // st0_expr.isTainted        = self.taintEngine.taintAssignment(st0, st0_addr);
    //         // st1_expr.isTainted        = self.taintEngine.taintAssignment(st1, st1_addr);
    //         // st2_expr.isTainted        = self.taintEngine.taintAssignment(st2, st2_addr);
    //         // st3_expr.isTainted        = self.taintEngine.taintAssignment(st3, st3_addr);
    //         // st4_expr.isTainted        = self.taintEngine.taintAssignment(st4, st4_addr);
    //         // st5_expr.isTainted        = self.taintEngine.taintAssignment(st5, st5_addr);
    //         // st6_expr.isTainted        = self.taintEngine.taintAssignment(st6, st6_addr);
    //         // st7_expr.isTainted        = self.taintEngine.taintAssignment(st7, st7_addr);
    //         // xmm0_expr.isTainted       = self.taintEngine.taintAssignment(xmm0, xmm0_addr);
    //         // xmm1_expr.isTainted       = self.taintEngine.taintAssignment(xmm1, xmm1_addr);
    //         // xmm2_expr.isTainted       = self.taintEngine.taintAssignment(xmm2, xmm2_addr);
    //         // xmm3_expr.isTainted       = self.taintEngine.taintAssignment(xmm3, xmm3_addr);
    //         // xmm4_expr.isTainted       = self.taintEngine.taintAssignment(xmm4, xmm4_addr);
    //         // xmm5_expr.isTainted       = self.taintEngine.taintAssignment(xmm5, xmm5_addr);
    //         // xmm6_expr.isTainted       = self.taintEngine.taintAssignment(xmm6, xmm6_addr);
    //         // xmm7_expr.isTainted       = self.taintEngine.taintAssignment(xmm7, xmm7_addr);

    //         /* Additional semantics, symbolic expressions and tainting for the '64-bit Mode Layout (with REX.W = 0)' */
    //         if (is64bits) {
    //           let xmm8  = Operand::Register(Register::XMM8);
    //           let xmm9  = Operand::Register(Register::XMM9);
    //           let xmm10 = Operand::Register(Register::XMM10);
    //           let xmm11 = Operand::Register(Register::XMM11);
    //           let xmm12 = Operand::Register(Register::XMM12);
    //           let xmm13 = Operand::Register(Register::XMM13);
    //           let xmm14 = Operand::Register(Register::XMM14);
    //           let xmm15 = Operand::Register(Register::XMM15);

    //           let xmm8_addr  = Operand::Memory(MemoryAccess::new(m512byte + 288, xmm8.getSize()));
    //           let xmm9_addr  = Operand::Memory(MemoryAccess::new(m512byte + 304, xmm9.getSize()));
    //           let xmm10_addr = Operand::Memory(MemoryAccess::new(m512byte + 320, xmm10.getSize()));
    //           let xmm11_addr = Operand::Memory(MemoryAccess::new(m512byte + 336, xmm11.getSize()));
    //           let xmm12_addr = Operand::Memory(MemoryAccess::new(m512byte + 352, xmm12.getSize()));
    //           let xmm13_addr = Operand::Memory(MemoryAccess::new(m512byte + 368, xmm13.getSize()));
    //           let xmm14_addr = Operand::Memory(MemoryAccess::new(m512byte + 384, xmm14.getSize()));
    //           let xmm15_addr = Operand::Memory(MemoryAccess::new(m512byte + 400, xmm15.getSize()));

    //           let xmm8_ast  = self.symbolicEngine.getOperandAst(inst, xmm8_addr);
    //           let xmm9_ast  = self.symbolicEngine.getOperandAst(inst, xmm9_addr);
    //           let xmm10_ast = self.symbolicEngine.getOperandAst(inst, xmm10_addr);
    //           let xmm11_ast = self.symbolicEngine.getOperandAst(inst, xmm11_addr);
    //           let xmm12_ast = self.symbolicEngine.getOperandAst(inst, xmm12_addr);
    //           let xmm13_ast = self.symbolicEngine.getOperandAst(inst, xmm13_addr);
    //           let xmm14_ast = self.symbolicEngine.getOperandAst(inst, xmm14_addr);
    //           let xmm15_ast = self.symbolicEngine.getOperandAst(inst, xmm15_addr);

    //           /* Fetch the original values for the XMM8-XMM15 registers */
    //           let xmm8_orig  = self.symbolicEngine.getOperandAst(inst, xmm8);
    //           let xmm9_orig  = self.symbolicEngine.getOperandAst(inst, xmm9);
    //           let xmm10_orig = self.symbolicEngine.getOperandAst(inst, xmm10);
    //           let xmm11_orig = self.symbolicEngine.getOperandAst(inst, xmm11);
    //           let xmm12_orig = self.symbolicEngine.getOperandAst(inst, xmm12);
    //           let xmm13_orig = self.symbolicEngine.getOperandAst(inst, xmm13);
    //           let xmm14_orig = self.symbolicEngine.getOperandAst(inst, xmm14);
    //           let xmm15_orig = self.symbolicEngine.getOperandAst(inst, xmm15);

    //           /* Apply the fast restore logic if needed */
    //           xmm8_ast  = self.ast_ctxt.ite(is_fast, xmm8_orig,  xmm8_ast);
    //           xmm9_ast  = self.ast_ctxt.ite(is_fast, xmm9_orig,  xmm9_ast);
    //           xmm10_ast = self.ast_ctxt.ite(is_fast, xmm10_orig, xmm10_ast);
    //           xmm11_ast = self.ast_ctxt.ite(is_fast, xmm11_orig, xmm11_ast);
    //           xmm12_ast = self.ast_ctxt.ite(is_fast, xmm12_orig, xmm12_ast);
    //           xmm13_ast = self.ast_ctxt.ite(is_fast, xmm13_orig, xmm13_ast);
    //           xmm14_ast = self.ast_ctxt.ite(is_fast, xmm14_orig, xmm14_ast);
    //           xmm15_ast = self.ast_ctxt.ite(is_fast, xmm15_orig, xmm15_ast);

    //           let xmm8_expr  = self.symbolicEngine.createSymbolicExpression(inst, xmm8_ast, xmm8, "FXRSTOR XMM8 operation");
    //           let xmm9_expr  = self.symbolicEngine.createSymbolicExpression(inst, xmm9_ast, xmm9, "FXRSTOR XMM9 operation");
    //           let xmm10_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm10_ast, xmm10, "FXRSTOR XMM10 operation");
    //           let xmm11_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm11_ast, xmm11, "FXRSTOR XMM11 operation");
    //           let xmm12_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm12_ast, xmm12, "FXRSTOR XMM12 operation");
    //           let xmm13_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm13_ast, xmm13, "FXRSTOR XMM13 operation");
    //           let xmm14_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm14_ast, xmm14, "FXRSTOR XMM14 operation");
    //           let xmm15_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm15_ast, xmm15, "FXRSTOR XMM15 operation");

    //         //   xmm8_expr.isTainted  = self.taintEngine.taintAssignment(xmm8, xmm8_addr);
    //         //   xmm9_expr.isTainted  = self.taintEngine.taintAssignment(xmm9, xmm9_addr);
    //         //   xmm10_expr.isTainted = self.taintEngine.taintAssignment(xmm10, xmm10_addr);
    //         //   xmm11_expr.isTainted = self.taintEngine.taintAssignment(xmm11, xmm11_addr);
    //         //   xmm12_expr.isTainted = self.taintEngine.taintAssignment(xmm12, xmm12_addr);
    //         //   xmm13_expr.isTainted = self.taintEngine.taintAssignment(xmm13, xmm13_addr);
    //         //   xmm14_expr.isTainted = self.taintEngine.taintAssignment(xmm14, xmm14_addr);
    //         //   xmm15_expr.isTainted = self.taintEngine.taintAssignment(xmm15, xmm15_addr);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn fxrstor64_s(&mut self, inst: x86Instruction) {
    //         /* Fetch the memory operand */
    //         let dst = inst.operands[0];
    //         let mem = dst.getMemory();
    //         let m512byte = mem.getAddress();

    //         /* Check if the address is on a 16-byte boundary */
    //         if (m512byte & 0xF) {
    //         //   self.exception = triton::arch::FAULT_GP;
    //           return;
    //         }

    //         /* Fetch the FPU, STX, SSE, EFER and CS implicit operands */
    //         let fcw         = Operand::Register(Register::FCW);
    //         let fsw         = Operand::Register(Register::FSW);
    //         let ftw         = Operand::Register(Register::FTW);
    //         let fop         = Operand::Register(Register::FOP);
    //         let fip         = Operand::Register(Register::FIP);
    //         let fcs         = Operand::Register(Register::FCS);
    //         let fdp         = Operand::Register(Register::FDP);
    //         let fds         = Operand::Register(Register::FDS);
    //         let mxcsr       = Operand::Register(Register::MXCSR);
    //         let mxcsr_mask  = Operand::Register(Register::MXCSR_MASK);
    //         let st0         = Operand::Register(Register::ST0);
    //         let st1         = Operand::Register(Register::ST1);
    //         let st2         = Operand::Register(Register::ST2);
    //         let st3         = Operand::Register(Register::ST3);
    //         let st4         = Operand::Register(Register::ST4);
    //         let st5         = Operand::Register(Register::ST5);
    //         let st6         = Operand::Register(Register::ST6);
    //         let st7         = Operand::Register(Register::ST7);
    //         let xmm0        = Operand::Register(Register::XMM0);
    //         let xmm1        = Operand::Register(Register::XMM1);
    //         let xmm2        = Operand::Register(Register::XMM2);
    //         let xmm3        = Operand::Register(Register::XMM3);
    //         let xmm4        = Operand::Register(Register::XMM4);
    //         let xmm5        = Operand::Register(Register::XMM5);
    //         let xmm6        = Operand::Register(Register::XMM6);
    //         let xmm7        = Operand::Register(Register::XMM7);
    //         let xmm8        = Operand::Register(Register::XMM8);
    //         let xmm9        = Operand::Register(Register::XMM9);
    //         let xmm10       = Operand::Register(Register::XMM10);
    //         let xmm11       = Operand::Register(Register::XMM11);
    //         let xmm12       = Operand::Register(Register::XMM12);
    //         let xmm13       = Operand::Register(Register::XMM13);
    //         let xmm14       = Operand::Register(Register::XMM14);
    //         let xmm15       = Operand::Register(Register::XMM15);
    //         let ffxsr       = Operand::Register(Register::EFER_FFXSR);
    //         let cs          = Operand::Register(Register::CS);

    //         /* Fetch the implicit memory slots for the '64-bit Mode Layout (with REX.W = 1)' */
    //         let fcw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 0, fcw.getSize()));
    //         let fsw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 2, fsw.getSize()));
    //         let ftw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 4, ftw.getSize() / 2));
    //         let fop_addr        = Operand::Memory(MemoryAccess::new(m512byte + 6, fop.getSize()));
    //         let fip_addr        = Operand::Memory(MemoryAccess::new(m512byte + 8, fip.getSize()));
    //         let fcs_addr        = Operand::Memory(MemoryAccess::new(m512byte + 12, fcs.getSize()));
    //         let fdp_addr        = Operand::Memory(MemoryAccess::new(m512byte + 16, fdp.getSize()));
    //         let fds_addr        = Operand::Memory(MemoryAccess::new(m512byte + 20, fds.getSize()));
    //         let mxcsr_addr      = Operand::Memory(MemoryAccess::new(m512byte + 24, mxcsr.getSize()));
    //         let mxcsr_mask_addr = Operand::Memory(MemoryAccess::new(m512byte + 28, mxcsr_mask.getSize()));
    //         let st0_addr        = Operand::Memory(MemoryAccess::new(m512byte + 32,  st0.getSize()));
    //         let st1_addr        = Operand::Memory(MemoryAccess::new(m512byte + 48,  st1.getSize()));
    //         let st2_addr        = Operand::Memory(MemoryAccess::new(m512byte + 64,  st2.getSize()));
    //         let st3_addr        = Operand::Memory(MemoryAccess::new(m512byte + 80,  st3.getSize()));
    //         let st4_addr        = Operand::Memory(MemoryAccess::new(m512byte + 96,  st4.getSize()));
    //         let st5_addr        = Operand::Memory(MemoryAccess::new(m512byte + 112, st5.getSize()));
    //         let st6_addr        = Operand::Memory(MemoryAccess::new(m512byte + 128, st6.getSize()));
    //         let st7_addr        = Operand::Memory(MemoryAccess::new(m512byte + 144, st7.getSize()));
    //         let xmm0_addr       = Operand::Memory(MemoryAccess::new(m512byte + 160, xmm0.getSize()));
    //         let xmm1_addr       = Operand::Memory(MemoryAccess::new(m512byte + 176, xmm1.getSize()));
    //         let xmm2_addr       = Operand::Memory(MemoryAccess::new(m512byte + 192, xmm2.getSize()));
    //         let xmm3_addr       = Operand::Memory(MemoryAccess::new(m512byte + 208, xmm3.getSize()));
    //         let xmm4_addr       = Operand::Memory(MemoryAccess::new(m512byte + 224, xmm4.getSize()));
    //         let xmm5_addr       = Operand::Memory(MemoryAccess::new(m512byte + 240, xmm5.getSize()));
    //         let xmm6_addr       = Operand::Memory(MemoryAccess::new(m512byte + 256, xmm6.getSize()));
    //         let xmm7_addr       = Operand::Memory(MemoryAccess::new(m512byte + 272, xmm7.getSize()));
    //         let xmm8_addr       = Operand::Memory(MemoryAccess::new(m512byte + 288, xmm8.getSize()));
    //         let xmm9_addr       = Operand::Memory(MemoryAccess::new(m512byte + 304, xmm9.getSize()));
    //         let xmm10_addr      = Operand::Memory(MemoryAccess::new(m512byte + 320, xmm10.getSize()));
    //         let xmm11_addr      = Operand::Memory(MemoryAccess::new(m512byte + 336, xmm11.getSize()));
    //         let xmm12_addr      = Operand::Memory(MemoryAccess::new(m512byte + 352, xmm12.getSize()));
    //         let xmm13_addr      = Operand::Memory(MemoryAccess::new(m512byte + 368, xmm13.getSize()));
    //         let xmm14_addr      = Operand::Memory(MemoryAccess::new(m512byte + 384, xmm14.getSize()));
    //         let xmm15_addr      = Operand::Memory(MemoryAccess::new(m512byte + 400, xmm15.getSize()));

    //         /* Create the symbolic operands */
    //         let fcw_ast        = self.symbolicEngine.getOperandAst(inst, fcw_addr);
    //         let fsw_ast        = self.symbolicEngine.getOperandAst(inst, fsw_addr);
    //         let ftw_ast        = self.symbolicEngine.getOperandAst(inst, ftw_addr);
    //         let fop_ast        = self.symbolicEngine.getOperandAst(inst, fop_addr);
    //         let fip_ast        = self.symbolicEngine.getOperandAst(inst, fip_addr);
    //         let fcs_ast        = self.symbolicEngine.getOperandAst(inst, fcs_addr);
    //         let fdp_ast        = self.symbolicEngine.getOperandAst(inst, fdp_addr);
    //         let fds_ast        = self.symbolicEngine.getOperandAst(inst, fds_addr);
    //         let mxcsr_ast      = self.symbolicEngine.getOperandAst(inst, mxcsr_addr);
    //         let mxcsr_mask_ast = self.symbolicEngine.getOperandAst(inst, mxcsr_mask_addr);
    //         let st0_ast        = self.symbolicEngine.getOperandAst(inst, st0_addr);
    //         let st1_ast        = self.symbolicEngine.getOperandAst(inst, st1_addr);
    //         let st2_ast        = self.symbolicEngine.getOperandAst(inst, st2_addr);
    //         let st3_ast        = self.symbolicEngine.getOperandAst(inst, st3_addr);
    //         let st4_ast        = self.symbolicEngine.getOperandAst(inst, st4_addr);
    //         let st5_ast        = self.symbolicEngine.getOperandAst(inst, st5_addr);
    //         let st6_ast        = self.symbolicEngine.getOperandAst(inst, st6_addr);
    //         let st7_ast        = self.symbolicEngine.getOperandAst(inst, st7_addr);
    //         let xmm0_ast       = self.symbolicEngine.getOperandAst(inst, xmm0_addr);
    //         let xmm1_ast       = self.symbolicEngine.getOperandAst(inst, xmm1_addr);
    //         let xmm2_ast       = self.symbolicEngine.getOperandAst(inst, xmm2_addr);
    //         let xmm3_ast       = self.symbolicEngine.getOperandAst(inst, xmm3_addr);
    //         let xmm4_ast       = self.symbolicEngine.getOperandAst(inst, xmm4_addr);
    //         let xmm5_ast       = self.symbolicEngine.getOperandAst(inst, xmm5_addr);
    //         let xmm6_ast       = self.symbolicEngine.getOperandAst(inst, xmm6_addr);
    //         let xmm7_ast       = self.symbolicEngine.getOperandAst(inst, xmm7_addr);
    //         let xmm8_ast       = self.symbolicEngine.getOperandAst(inst, xmm8_addr);
    //         let xmm9_ast       = self.symbolicEngine.getOperandAst(inst, xmm9_addr);
    //         let xmm10_ast      = self.symbolicEngine.getOperandAst(inst, xmm10_addr);
    //         let xmm11_ast      = self.symbolicEngine.getOperandAst(inst, xmm11_addr);
    //         let xmm12_ast      = self.symbolicEngine.getOperandAst(inst, xmm12_addr);
    //         let xmm13_ast      = self.symbolicEngine.getOperandAst(inst, xmm13_addr);
    //         let xmm14_ast      = self.symbolicEngine.getOperandAst(inst, xmm14_addr);
    //         let xmm15_ast      = self.symbolicEngine.getOperandAst(inst, xmm15_addr);
    //         let ffxsr_ast      = self.symbolicEngine.getOperandAst(inst, ffxsr);
    //         let cs_ast         = self.symbolicEngine.getOperandAst(inst, cs);

    //         /* Fetch the original values for the XMM0-XMM15 registers */
    //         let xmm0_orig  = self.symbolicEngine.getOperandAst(inst, xmm0);
    //         let xmm1_orig  = self.symbolicEngine.getOperandAst(inst, xmm1);
    //         let xmm2_orig  = self.symbolicEngine.getOperandAst(inst, xmm2);
    //         let xmm3_orig  = self.symbolicEngine.getOperandAst(inst, xmm3);
    //         let xmm4_orig  = self.symbolicEngine.getOperandAst(inst, xmm4);
    //         let xmm5_orig  = self.symbolicEngine.getOperandAst(inst, xmm5);
    //         let xmm6_orig  = self.symbolicEngine.getOperandAst(inst, xmm6);
    //         let xmm7_orig  = self.symbolicEngine.getOperandAst(inst, xmm7);
    //         let xmm8_orig  = self.symbolicEngine.getOperandAst(inst, xmm8);
    //         let xmm9_orig  = self.symbolicEngine.getOperandAst(inst, xmm9);
    //         let xmm10_orig = self.symbolicEngine.getOperandAst(inst, xmm10);
    //         let xmm11_orig = self.symbolicEngine.getOperandAst(inst, xmm11);
    //         let xmm12_orig = self.symbolicEngine.getOperandAst(inst, xmm12);
    //         let xmm13_orig = self.symbolicEngine.getOperandAst(inst, xmm13);
    //         let xmm14_orig = self.symbolicEngine.getOperandAst(inst, xmm14);
    //         let xmm15_orig = self.symbolicEngine.getOperandAst(inst, xmm15);

    //         /* Check if we are running in CPL = 0 (ring 0) and if the FFXSR bit is set in EFER */
    //         let cpl     = self.ast_ctxt.equal(self.ast_ctxt.extract(1, 0, cs_ast), self.ast_ctxt.bv(0, 2));
    //         let ffx     = self.ast_ctxt.equal(ffxsr_ast, self.ast_ctxt.bv(1, 1));
    //         let is_fast = self.ast_ctxt.land(cpl, ffx);

    //         /* Apply the fast restore logic if needed */
    //         xmm0_ast  = self.ast_ctxt.ite(is_fast, xmm0_orig,  xmm0_ast);
    //         xmm1_ast  = self.ast_ctxt.ite(is_fast, xmm1_orig,  xmm1_ast);
    //         xmm2_ast  = self.ast_ctxt.ite(is_fast, xmm2_orig,  xmm2_ast);
    //         xmm3_ast  = self.ast_ctxt.ite(is_fast, xmm3_orig,  xmm3_ast);
    //         xmm4_ast  = self.ast_ctxt.ite(is_fast, xmm4_orig,  xmm4_ast);
    //         xmm5_ast  = self.ast_ctxt.ite(is_fast, xmm5_orig,  xmm5_ast);
    //         xmm6_ast  = self.ast_ctxt.ite(is_fast, xmm6_orig,  xmm6_ast);
    //         xmm7_ast  = self.ast_ctxt.ite(is_fast, xmm7_orig,  xmm7_ast);
    //         xmm8_ast  = self.ast_ctxt.ite(is_fast, xmm8_orig,  xmm8_ast);
    //         xmm9_ast  = self.ast_ctxt.ite(is_fast, xmm9_orig,  xmm9_ast);
    //         xmm10_ast = self.ast_ctxt.ite(is_fast, xmm10_orig, xmm10_ast);
    //         xmm11_ast = self.ast_ctxt.ite(is_fast, xmm11_orig, xmm11_ast);
    //         xmm12_ast = self.ast_ctxt.ite(is_fast, xmm12_orig, xmm12_ast);
    //         xmm13_ast = self.ast_ctxt.ite(is_fast, xmm13_orig, xmm13_ast);
    //         xmm14_ast = self.ast_ctxt.ite(is_fast, xmm14_orig, xmm14_ast);
    //         xmm15_ast = self.ast_ctxt.ite(is_fast, xmm15_orig, xmm15_ast);

    //         /* Fetch the abridged x87 FPU Tag Word Encoded Bits */
    //         let eb_1_0   = self.ast_ctxt.extract(0, 0, ftw_ast);
    //         let eb_3_2   = self.ast_ctxt.extract(1, 1, ftw_ast);
    //         let eb_5_4   = self.ast_ctxt.extract(2, 2, ftw_ast);
    //         let eb_7_6   = self.ast_ctxt.extract(3, 3, ftw_ast);
    //         let eb_9_8   = self.ast_ctxt.extract(4, 4, ftw_ast);
    //         let eb_11_10 = self.ast_ctxt.extract(5, 5, ftw_ast);
    //         let eb_13_12 = self.ast_ctxt.extract(6, 6, ftw_ast);
    //         let eb_15_14 = self.ast_ctxt.extract(7, 7, ftw_ast);

    //         /* Extract the fraction from the STX registers */
    //         let fraction_st0 = self.ast_ctxt.extract(62, 0, st0_ast);
    //         let fraction_st1 = self.ast_ctxt.extract(62, 0, st1_ast);
    //         let fraction_st2 = self.ast_ctxt.extract(62, 0, st2_ast);
    //         let fraction_st3 = self.ast_ctxt.extract(62, 0, st3_ast);
    //         let fraction_st4 = self.ast_ctxt.extract(62, 0, st4_ast);
    //         let fraction_st5 = self.ast_ctxt.extract(62, 0, st5_ast);
    //         let fraction_st6 = self.ast_ctxt.extract(62, 0, st6_ast);
    //         let fraction_st7 = self.ast_ctxt.extract(62, 0, st7_ast);

    //         /* Extract the integer bit from the STX registers */
    //         let integer_st0 = self.ast_ctxt.extract(63, 63, st0_ast);
    //         let integer_st1 = self.ast_ctxt.extract(63, 63, st1_ast);
    //         let integer_st2 = self.ast_ctxt.extract(63, 63, st2_ast);
    //         let integer_st3 = self.ast_ctxt.extract(63, 63, st3_ast);
    //         let integer_st4 = self.ast_ctxt.extract(63, 63, st4_ast);
    //         let integer_st5 = self.ast_ctxt.extract(63, 63, st5_ast);
    //         let integer_st6 = self.ast_ctxt.extract(63, 63, st6_ast);
    //         let integer_st7 = self.ast_ctxt.extract(63, 63, st7_ast);

    //         /* Extract the exponent from the STX registers */
    //         let exponent_st0 = self.ast_ctxt.extract(79, 64, st0_ast);
    //         let exponent_st1 = self.ast_ctxt.extract(79, 64, st1_ast);
    //         let exponent_st2 = self.ast_ctxt.extract(79, 64, st2_ast);
    //         let exponent_st3 = self.ast_ctxt.extract(79, 64, st3_ast);
    //         let exponent_st4 = self.ast_ctxt.extract(79, 64, st4_ast);
    //         let exponent_st5 = self.ast_ctxt.extract(79, 64, st5_ast);
    //         let exponent_st6 = self.ast_ctxt.extract(79, 64, st6_ast);
    //         let exponent_st7 = self.ast_ctxt.extract(79, 64, st7_ast);

    //         /* Exponent All Zeros */
    //         let ea0_st0 = self.ast_ctxt.equal(exponent_st0, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st1 = self.ast_ctxt.equal(exponent_st1, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st2 = self.ast_ctxt.equal(exponent_st2, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st3 = self.ast_ctxt.equal(exponent_st3, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st4 = self.ast_ctxt.equal(exponent_st4, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st5 = self.ast_ctxt.equal(exponent_st5, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st6 = self.ast_ctxt.equal(exponent_st6, self.ast_ctxt.bv(0x0000, 16));
    //         let ea0_st7 = self.ast_ctxt.equal(exponent_st7, self.ast_ctxt.bv(0x0000, 16));

    //         /* Exponent All Ones */
    //         let ea1_st0 = self.ast_ctxt.equal(exponent_st0, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st1 = self.ast_ctxt.equal(exponent_st1, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st2 = self.ast_ctxt.equal(exponent_st2, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st3 = self.ast_ctxt.equal(exponent_st3, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st4 = self.ast_ctxt.equal(exponent_st4, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st5 = self.ast_ctxt.equal(exponent_st5, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st6 = self.ast_ctxt.equal(exponent_st6, self.ast_ctxt.bv(0xFFFF, 16));
    //         let ea1_st7 = self.ast_ctxt.equal(exponent_st7, self.ast_ctxt.bv(0xFFFF, 16));

    //         /* Exponent Neither All Zeroes Or Ones */
    //         let ena01_st0 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st0, ea1_st0), self.ast_ctxt.bvfalse());
    //         let ena01_st1 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st1, ea1_st1), self.ast_ctxt.bvfalse());
    //         let ena01_st2 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st2, ea1_st2), self.ast_ctxt.bvfalse());
    //         let ena01_st3 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st3, ea1_st3), self.ast_ctxt.bvfalse());
    //         let ena01_st4 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st4, ea1_st4), self.ast_ctxt.bvfalse());
    //         let ena01_st5 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st5, ea1_st5), self.ast_ctxt.bvfalse());
    //         let ena01_st6 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st6, ea1_st6), self.ast_ctxt.bvfalse());
    //         let ena01_st7 = self.ast_ctxt.equal(self.ast_ctxt.lor(ea0_st7, ea1_st7), self.ast_ctxt.bvfalse());

    //         /* Integer Bit 0 */
    //         let ib0_st0 = self.ast_ctxt.equal(integer_st0, self.ast_ctxt.bv(0, 1));
    //         let ib0_st1 = self.ast_ctxt.equal(integer_st1, self.ast_ctxt.bv(0, 1));
    //         let ib0_st2 = self.ast_ctxt.equal(integer_st2, self.ast_ctxt.bv(0, 1));
    //         let ib0_st3 = self.ast_ctxt.equal(integer_st3, self.ast_ctxt.bv(0, 1));
    //         let ib0_st4 = self.ast_ctxt.equal(integer_st4, self.ast_ctxt.bv(0, 1));
    //         let ib0_st5 = self.ast_ctxt.equal(integer_st5, self.ast_ctxt.bv(0, 1));
    //         let ib0_st6 = self.ast_ctxt.equal(integer_st6, self.ast_ctxt.bv(0, 1));
    //         let ib0_st7 = self.ast_ctxt.equal(integer_st7, self.ast_ctxt.bv(0, 1));

    //         /* Fraction All Zeroes */
    //         let fa0_st0 = self.ast_ctxt.equal(fraction_st0, self.ast_ctxt.bv(0, 63));
    //         let fa0_st1 = self.ast_ctxt.equal(fraction_st1, self.ast_ctxt.bv(0, 63));
    //         let fa0_st2 = self.ast_ctxt.equal(fraction_st2, self.ast_ctxt.bv(0, 63));
    //         let fa0_st3 = self.ast_ctxt.equal(fraction_st3, self.ast_ctxt.bv(0, 63));
    //         let fa0_st4 = self.ast_ctxt.equal(fraction_st4, self.ast_ctxt.bv(0, 63));
    //         let fa0_st5 = self.ast_ctxt.equal(fraction_st5, self.ast_ctxt.bv(0, 63));
    //         let fa0_st6 = self.ast_ctxt.equal(fraction_st6, self.ast_ctxt.bv(0, 63));
    //         let fa0_st7 = self.ast_ctxt.equal(fraction_st7, self.ast_ctxt.bv(0, 63));

    //         /* Determine the x87 FPU Tag Word (Diagram at page 379 of the AMD Architecture Programmer's Manual, Volume 2: System Programming) */
    //         let db_1_0 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_1_0, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st0,
    //             self.ast_ctxt.ite(ib0_st0,
    //               self.ast_ctxt.ite(fa0_st0,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st0,
    //               self.ast_ctxt.ite(ib0_st0,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_3_2 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_3_2, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st1,
    //             self.ast_ctxt.ite(ib0_st1,
    //               self.ast_ctxt.ite(fa0_st1,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st1,
    //               self.ast_ctxt.ite(ib0_st1,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_5_4 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_5_4, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st2,
    //             self.ast_ctxt.ite(ib0_st2,
    //               self.ast_ctxt.ite(fa0_st2,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st2,
    //               self.ast_ctxt.ite(ib0_st2,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_7_6 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_7_6, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st3,
    //             self.ast_ctxt.ite(ib0_st3,
    //               self.ast_ctxt.ite(fa0_st3,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st3,
    //               self.ast_ctxt.ite(ib0_st3,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_9_8 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_9_8, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st4,
    //             self.ast_ctxt.ite(ib0_st4,
    //               self.ast_ctxt.ite(fa0_st4,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st4,
    //               self.ast_ctxt.ite(ib0_st4,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_11_10 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_11_10, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st5,
    //             self.ast_ctxt.ite(ib0_st5,
    //               self.ast_ctxt.ite(fa0_st5,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st5,
    //               self.ast_ctxt.ite(ib0_st5,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_13_12 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_13_12, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st6,
    //             self.ast_ctxt.ite(ib0_st6,
    //               self.ast_ctxt.ite(fa0_st6,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st6,
    //               self.ast_ctxt.ite(ib0_st6,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         let db_15_14 = self.ast_ctxt.ite(self.ast_ctxt.equal(eb_15_14, self.ast_ctxt.bv(0, 1)),
    //           self.ast_ctxt.bv(3, 2),          // Encoded x87 FPU Tag Bit = 0
    //           self.ast_ctxt.ite(ea0_st7,
    //             self.ast_ctxt.ite(ib0_st7,
    //               self.ast_ctxt.ite(fa0_st7,
    //                 self.ast_ctxt.bv(1, 2),    // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction All 0'
    //                 self.ast_ctxt.bv(2, 2)),   // 'Exponent All 0' + 'Integer Bit 0' + 'Fraction Not All 0'
    //               self.ast_ctxt.bv(2, 2)),     // 'Exponent All 0' + 'Integer Bit 1'
    //             self.ast_ctxt.ite(ena01_st7,
    //               self.ast_ctxt.ite(ib0_st7,
    //                 self.ast_ctxt.bv(2, 2),    // 'Exponent Not All 0/1' + 'Integer Bit 0'
    //                 self.ast_ctxt.bv(0, 2)),   // 'Exponent Not All 0/1' + 'Integer Bit 1'
    //               self.ast_ctxt.bv(2, 2))));   // 'Exponent All 1'

    //         /* Restore the x87 FPU Tag Word */
    //         let uftw_ast = self.ast_ctxt.concat(db_15_14,
    //           self.ast_ctxt.concat(db_13_12,
    //           self.ast_ctxt.concat(db_11_10,
    //           self.ast_ctxt.concat(db_9_8,
    //           self.ast_ctxt.concat(db_7_6,
    //           self.ast_ctxt.concat(db_5_4,
    //           self.ast_ctxt.concat(db_3_2, db_1_0)))))));

    //         /* Craft the symbolic expressions */
    //         let fcw_expr        = self.symbolicEngine.createSymbolicExpression(inst, fcw_ast, fcw, "FXRSTOR64 FCW operation");
    //         let fsw_expr        = self.symbolicEngine.createSymbolicExpression(inst, fsw_ast, fsw, "FXRSTOR64 FSW operation");
    //         let ftw_expr        = self.symbolicEngine.createSymbolicExpression(inst, uftw_ast, ftw, "FXRSTOR64 Updated FTW operation");
    //         let fop_expr        = self.symbolicEngine.createSymbolicExpression(inst, fop_ast, fop, "FXRSTOR64 FOP operation");
    //         let fip_expr        = self.symbolicEngine.createSymbolicExpression(inst, fip_ast, fip, "FXRSTOR64 FIP operation");
    //         let fcs_expr        = self.symbolicEngine.createSymbolicExpression(inst, fcs_ast, fcs, "FXRSTOR64 FCS operation");
    //         let fdp_expr        = self.symbolicEngine.createSymbolicExpression(inst, fdp_ast, fdp, "FXRSTOR64 FDP operation");
    //         let fds_expr        = self.symbolicEngine.createSymbolicExpression(inst, fds_ast, fds, "FXRSTOR64 FDS operation");
    //         let mxcsr_expr      = self.symbolicEngine.createSymbolicExpression(inst, mxcsr_ast, mxcsr, "FXRSTOR64 MXCSR operation");
    //         let mxcsr_mask_expr = self.symbolicEngine.createSymbolicExpression(inst, mxcsr_mask_ast, mxcsr_mask, "FXRSTOR64 MXCSR_MASK operation");
    //         let st0_expr        = self.symbolicEngine.createSymbolicExpression(inst, st0_ast, st0, "FXRSTOR64 ST0 operation");
    //         let st1_expr        = self.symbolicEngine.createSymbolicExpression(inst, st1_ast, st1, "FXRSTOR64 ST1 operation");
    //         let st2_expr        = self.symbolicEngine.createSymbolicExpression(inst, st2_ast, st2, "FXRSTOR64 ST2 operation");
    //         let st3_expr        = self.symbolicEngine.createSymbolicExpression(inst, st3_ast, st3, "FXRSTOR64 ST3 operation");
    //         let st4_expr        = self.symbolicEngine.createSymbolicExpression(inst, st4_ast, st4, "FXRSTOR64 ST4 operation");
    //         let st5_expr        = self.symbolicEngine.createSymbolicExpression(inst, st5_ast, st5, "FXRSTOR64 ST5 operation");
    //         let st6_expr        = self.symbolicEngine.createSymbolicExpression(inst, st6_ast, st6, "FXRSTOR64 ST6 operation");
    //         let st7_expr        = self.symbolicEngine.createSymbolicExpression(inst, st7_ast, st7, "FXRSTOR64 ST7 operation");
    //         let xmm0_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm0_ast, xmm0, "FXRSTOR64 XMM0 operation");
    //         let xmm1_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm1_ast, xmm1, "FXRSTOR64 XMM1 operation");
    //         let xmm2_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm2_ast, xmm2, "FXRSTOR64 XMM2 operation");
    //         let xmm3_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm3_ast, xmm3, "FXRSTOR64 XMM3 operation");
    //         let xmm4_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm4_ast, xmm4, "FXRSTOR64 XMM4 operation");
    //         let xmm5_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm5_ast, xmm5, "FXRSTOR64 XMM5 operation");
    //         let xmm6_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm6_ast, xmm6, "FXRSTOR64 XMM6 operation");
    //         let xmm7_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm7_ast, xmm7, "FXRSTOR64 XMM7 operation");
    //         let xmm8_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm8_ast, xmm8, "FXRSTOR64 XMM8 operation");
    //         let xmm9_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm9_ast, xmm9, "FXRSTOR64 XMM9 operation");
    //         let xmm10_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm10_ast, xmm10, "FXRSTOR64 XMM10 operation");
    //         let xmm11_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm11_ast, xmm11, "FXRSTOR64 XMM11 operation");
    //         let xmm12_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm12_ast, xmm12, "FXRSTOR64 XMM12 operation");
    //         let xmm13_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm13_ast, xmm13, "FXRSTOR64 XMM13 operation");
    //         let xmm14_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm14_ast, xmm14, "FXRSTOR64 XMM14 operation");
    //         let xmm15_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm15_ast, xmm15, "FXRSTOR64 XMM15 operation");

    //         /* Spread the taint */
    //         // fcw_expr.isTainted        = self.taintEngine.taintAssignment(fcw, fcw_addr);
    //         // fsw_expr.isTainted        = self.taintEngine.taintAssignment(fsw, fsw_addr);
    //         // ftw_expr.isTainted        = self.taintEngine.taintAssignment(ftw, ftw_addr);
    //         // fop_expr.isTainted        = self.taintEngine.taintAssignment(fop, fop_addr);
    //         // fip_expr.isTainted        = self.taintEngine.taintAssignment(fip, fip_addr);
    //         // fcs_expr.isTainted        = self.taintEngine.taintAssignment(fcs, fcs_addr);
    //         // fdp_expr.isTainted        = self.taintEngine.taintAssignment(fdp, fdp_addr);
    //         // fds_expr.isTainted        = self.taintEngine.taintAssignment(fds, fds_addr);
    //         // mxcsr_expr.isTainted      = self.taintEngine.taintAssignment(mxcsr, mxcsr_addr);
    //         // mxcsr_mask_expr.isTainted = self.taintEngine.taintAssignment(mxcsr_mask, mxcsr_mask_addr);
    //         // st0_expr.isTainted        = self.taintEngine.taintAssignment(st0, st0_addr);
    //         // st1_expr.isTainted        = self.taintEngine.taintAssignment(st1, st1_addr);
    //         // st2_expr.isTainted        = self.taintEngine.taintAssignment(st2, st2_addr);
    //         // st3_expr.isTainted        = self.taintEngine.taintAssignment(st3, st3_addr);
    //         // st4_expr.isTainted        = self.taintEngine.taintAssignment(st4, st4_addr);
    //         // st5_expr.isTainted        = self.taintEngine.taintAssignment(st5, st5_addr);
    //         // st6_expr.isTainted        = self.taintEngine.taintAssignment(st6, st6_addr);
    //         // st7_expr.isTainted        = self.taintEngine.taintAssignment(st7, st7_addr);
    //         // xmm0_expr.isTainted       = self.taintEngine.taintAssignment(xmm0, xmm0_addr);
    //         // xmm1_expr.isTainted       = self.taintEngine.taintAssignment(xmm1, xmm1_addr);
    //         // xmm2_expr.isTainted       = self.taintEngine.taintAssignment(xmm2, xmm2_addr);
    //         // xmm3_expr.isTainted       = self.taintEngine.taintAssignment(xmm3, xmm3_addr);
    //         // xmm4_expr.isTainted       = self.taintEngine.taintAssignment(xmm4, xmm4_addr);
    //         // xmm5_expr.isTainted       = self.taintEngine.taintAssignment(xmm5, xmm5_addr);
    //         // xmm6_expr.isTainted       = self.taintEngine.taintAssignment(xmm6, xmm6_addr);
    //         // xmm7_expr.isTainted       = self.taintEngine.taintAssignment(xmm7, xmm7_addr);
    //         // xmm8_expr.isTainted       = self.taintEngine.taintAssignment(xmm8, xmm8_addr);
    //         // xmm9_expr.isTainted       = self.taintEngine.taintAssignment(xmm9, xmm9_addr);
    //         // xmm10_expr.isTainted      = self.taintEngine.taintAssignment(xmm10, xmm10_addr);
    //         // xmm11_expr.isTainted      = self.taintEngine.taintAssignment(xmm11, xmm11_addr);
    //         // xmm12_expr.isTainted      = self.taintEngine.taintAssignment(xmm12, xmm12_addr);
    //         // xmm13_expr.isTainted      = self.taintEngine.taintAssignment(xmm13, xmm13_addr);
    //         // xmm14_expr.isTainted      = self.taintEngine.taintAssignment(xmm14, xmm14_addr);
    //         // xmm15_expr.isTainted      = self.taintEngine.taintAssignment(xmm15, xmm15_addr);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn fxsave_s(&mut self, inst: x86Instruction) {
    //         /* Fetch the current architecture */
    //         let arch = self.architecture.getArchitecture();

    //         /* Determine if we are executing in 64 bit mode */
    //         let is64bits = arch == triton::arch::architecture_e::ARCH_X86_64;

    //         /* Fetch the memory operand */
    //         let dst = inst.operands[0];
    //         let mem = dst.getMemory();
    //         let m512byte = mem.getAddress();

    //         /* Check if the address is on a 16-byte boundary */
    //         if (m512byte & 0xF) {
    //         //   self.exception = triton::arch::FAULT_GP;
    //           return;
    //         }

    //         /* Fetch the FPU, STX, SSE, EFER and CS implicit operands */
    //         let fcw        = Operand::Register(Register::FCW);
    //         let fsw        = Operand::Register(Register::FSW);
    //         let ftw        = Operand::Register(Register::FTW);
    //         let fop        = Operand::Register(Register::FOP);
    //         let fip        = Operand::Register(Register::FIP);
    //         let fcs        = Operand::Register(Register::FCS);
    //         let fdp        = Operand::Register(Register::FDP);
    //         let fds        = Operand::Register(Register::FDS);
    //         let mxcsr      = Operand::Register(Register::MXCSR);
    //         let mxcsr_mask = Operand::Register(Register::MXCSR_MASK);
    //         let st0        = Operand::Register(Register::ST0);
    //         let st1        = Operand::Register(Register::ST1);
    //         let st2        = Operand::Register(Register::ST2);
    //         let st3        = Operand::Register(Register::ST3);
    //         let st4        = Operand::Register(Register::ST4);
    //         let st5        = Operand::Register(Register::ST5);
    //         let st6        = Operand::Register(Register::ST6);
    //         let st7        = Operand::Register(Register::ST7);
    //         let xmm0       = Operand::Register(Register::XMM0);
    //         let xmm1       = Operand::Register(Register::XMM1);
    //         let xmm2       = Operand::Register(Register::XMM2);
    //         let xmm3       = Operand::Register(Register::XMM3);
    //         let xmm4       = Operand::Register(Register::XMM4);
    //         let xmm5       = Operand::Register(Register::XMM5);
    //         let xmm6       = Operand::Register(Register::XMM6);
    //         let xmm7       = Operand::Register(Register::XMM7);
    //         let ffxsr      = Operand::Register(Register::EFER_FFXSR);
    //         let cs         = Operand::Register(Register::CS);

    //         /* Create the symbolic operands */
    //         let fcw_ast        = self.symbolicEngine.getOperandAst(inst, fcw);
    //         let fsw_ast        = self.symbolicEngine.getOperandAst(inst, fsw);
    //         let ftw_ast        = self.symbolicEngine.getOperandAst(inst, ftw);
    //         let fop_ast        = self.symbolicEngine.getOperandAst(inst, fop);
    //         let fip_ast        = self.ast_ctxt.extract(BitSizes::DWORD - 1, 0, self.symbolicEngine.getOperandAst(inst, fip));
    //         let fcs_ast        = self.symbolicEngine.getOperandAst(inst, fcs);
    //         let fdp_ast        = self.ast_ctxt.extract(BitSizes::DWORD - 1, 0, self.symbolicEngine.getOperandAst(inst, fdp));
    //         let fds_ast        = self.symbolicEngine.getOperandAst(inst, fds);
    //         let mxcsr_ast      = self.symbolicEngine.getOperandAst(inst, mxcsr);
    //         let mxcsr_mask_ast = self.symbolicEngine.getOperandAst(inst, mxcsr_mask);
    //         let st0_ast        = self.symbolicEngine.getOperandAst(inst, st0);
    //         let st1_ast        = self.symbolicEngine.getOperandAst(inst, st1);
    //         let st2_ast        = self.symbolicEngine.getOperandAst(inst, st2);
    //         let st3_ast        = self.symbolicEngine.getOperandAst(inst, st3);
    //         let st4_ast        = self.symbolicEngine.getOperandAst(inst, st4);
    //         let st5_ast        = self.symbolicEngine.getOperandAst(inst, st5);
    //         let st6_ast        = self.symbolicEngine.getOperandAst(inst, st6);
    //         let st7_ast        = self.symbolicEngine.getOperandAst(inst, st7);
    //         let xmm0_ast       = self.symbolicEngine.getOperandAst(inst, xmm0);
    //         let xmm1_ast       = self.symbolicEngine.getOperandAst(inst, xmm1);
    //         let xmm2_ast       = self.symbolicEngine.getOperandAst(inst, xmm2);
    //         let xmm3_ast       = self.symbolicEngine.getOperandAst(inst, xmm3);
    //         let xmm4_ast       = self.symbolicEngine.getOperandAst(inst, xmm4);
    //         let xmm5_ast       = self.symbolicEngine.getOperandAst(inst, xmm5);
    //         let xmm6_ast       = self.symbolicEngine.getOperandAst(inst, xmm6);
    //         let xmm7_ast       = self.symbolicEngine.getOperandAst(inst, xmm7);
    //         let ffxsr_ast      = self.symbolicEngine.getOperandAst(inst, ffxsr);
    //         let cs_ast         = self.symbolicEngine.getOperandAst(inst, cs);

    //         /*
    //           Calculate the abridged x87 FPU Tag Word (from 2 bytes to 1 byte encoding)
    //           - Two-bit values of 00, 01, and 10 are encoded as a 1
    //           - A two-bit value of 11 is encoded as a 0
    //         */
    //         let eb_1_0 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(1, 0, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_3_2 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(3, 2, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_5_4 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(5, 4, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_7_6 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(7, 6, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_9_8 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(9, 8, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_11_10 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(11, 10, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_13_12 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(13, 12, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_15_14 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(15, 14, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let aftw_ast = self.ast_ctxt.concat(eb_15_14,
    //           self.ast_ctxt.concat(eb_13_12,
    //           self.ast_ctxt.concat(eb_11_10,
    //           self.ast_ctxt.concat(eb_9_8,
    //           self.ast_ctxt.concat(eb_7_6,
    //           self.ast_ctxt.concat(eb_5_4,
    //           self.ast_ctxt.concat(eb_3_2, eb_1_0)))))));

    //         /* Fetch the implicit memory slots for the 'Non-64-bit Mode Layout' */
    //         let fcw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 0, fcw.getSize()));
    //         let fsw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 2, fsw.getSize()));
    //         let ftw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 4, ftw.getSize() / 2));
    //         let fop_addr        = Operand::Memory(MemoryAccess::new(m512byte + 6, fop.getSize()));
    //         let fip_addr        = Operand::Memory(MemoryAccess::new(m512byte + 8, fip.getSize() / 2));
    //         let fcs_addr        = Operand::Memory(MemoryAccess::new(m512byte + 12, fcs.getSize()));
    //         let fdp_addr        = Operand::Memory(MemoryAccess::new(m512byte + 16, fdp.getSize() / 2));
    //         let fds_addr        = Operand::Memory(MemoryAccess::new(m512byte + 20, fds.getSize()));
    //         let mxcsr_addr      = Operand::Memory(MemoryAccess::new(m512byte + 24, mxcsr.getSize()));
    //         let mxcsr_mask_addr = Operand::Memory(MemoryAccess::new(m512byte + 28, mxcsr_mask.getSize()));
    //         let st0_addr        = Operand::Memory(MemoryAccess::new(m512byte + 32,  st0.getSize()));
    //         let st1_addr        = Operand::Memory(MemoryAccess::new(m512byte + 48,  st1.getSize()));
    //         let st2_addr        = Operand::Memory(MemoryAccess::new(m512byte + 64,  st2.getSize()));
    //         let st3_addr        = Operand::Memory(MemoryAccess::new(m512byte + 80,  st3.getSize()));
    //         let st4_addr        = Operand::Memory(MemoryAccess::new(m512byte + 96,  st4.getSize()));
    //         let st5_addr        = Operand::Memory(MemoryAccess::new(m512byte + 112, st5.getSize()));
    //         let st6_addr        = Operand::Memory(MemoryAccess::new(m512byte + 128, st6.getSize()));
    //         let st7_addr        = Operand::Memory(MemoryAccess::new(m512byte + 144, st7.getSize()));
    //         let xmm0_addr       = Operand::Memory(MemoryAccess::new(m512byte + 160, xmm0.getSize()));
    //         let xmm1_addr       = Operand::Memory(MemoryAccess::new(m512byte + 176, xmm1.getSize()));
    //         let xmm2_addr       = Operand::Memory(MemoryAccess::new(m512byte + 192, xmm2.getSize()));
    //         let xmm3_addr       = Operand::Memory(MemoryAccess::new(m512byte + 208, xmm3.getSize()));
    //         let xmm4_addr       = Operand::Memory(MemoryAccess::new(m512byte + 224, xmm4.getSize()));
    //         let xmm5_addr       = Operand::Memory(MemoryAccess::new(m512byte + 240, xmm5.getSize()));
    //         let xmm6_addr       = Operand::Memory(MemoryAccess::new(m512byte + 256, xmm6.getSize()));
    //         let xmm7_addr       = Operand::Memory(MemoryAccess::new(m512byte + 272, xmm7.getSize()));

    //         /* Fetch the original values of the XMM0-XMM7 memory spaces */
    //         let xmm0_orig = self.symbolicEngine.getOperandAst(xmm0_addr);
    //         let xmm1_orig = self.symbolicEngine.getOperandAst(xmm1_addr);
    //         let xmm2_orig = self.symbolicEngine.getOperandAst(xmm2_addr);
    //         let xmm3_orig = self.symbolicEngine.getOperandAst(xmm3_addr);
    //         let xmm4_orig = self.symbolicEngine.getOperandAst(xmm4_addr);
    //         let xmm5_orig = self.symbolicEngine.getOperandAst(xmm5_addr);
    //         let xmm6_orig = self.symbolicEngine.getOperandAst(xmm6_addr);
    //         let xmm7_orig = self.symbolicEngine.getOperandAst(xmm7_addr);

    //         /* Check if we are running in CPL = 0 (ring 0) and if the FFXSR bit is set in EFER */
    //         let cpl     = self.ast_ctxt.equal(self.ast_ctxt.extract(1, 0, cs_ast), self.ast_ctxt.bv(0, 2));
    //         let ffx     = self.ast_ctxt.equal(ffxsr_ast, self.ast_ctxt.bv(1, 1));
    //         let b64     = self.ast_ctxt.equal(self.ast_ctxt.bv(is64bits, 1), self.ast_ctxt.bv(1, 1));
    //         let is_fast = self.ast_ctxt.land(self.ast_ctxt.land(cpl, ffx), b64);

    //         /* Apply the fast save logic if needed */
    //         xmm0_ast  = self.ast_ctxt.ite(is_fast, xmm0_orig,  xmm0_ast);
    //         xmm1_ast  = self.ast_ctxt.ite(is_fast, xmm1_orig,  xmm1_ast);
    //         xmm2_ast  = self.ast_ctxt.ite(is_fast, xmm2_orig,  xmm2_ast);
    //         xmm3_ast  = self.ast_ctxt.ite(is_fast, xmm3_orig,  xmm3_ast);
    //         xmm4_ast  = self.ast_ctxt.ite(is_fast, xmm4_orig,  xmm4_ast);
    //         xmm5_ast  = self.ast_ctxt.ite(is_fast, xmm5_orig,  xmm5_ast);
    //         xmm6_ast  = self.ast_ctxt.ite(is_fast, xmm6_orig,  xmm6_ast);
    //         xmm7_ast  = self.ast_ctxt.ite(is_fast, xmm7_orig,  xmm7_ast);

    //         /* Craft the symbolic expressions */
    //         let fcw_expr        = self.symbolicEngine.createSymbolicExpression(inst, fcw_ast, fcw_addr, "FXSAVE FCW operation");
    //         let fsw_expr        = self.symbolicEngine.createSymbolicExpression(inst, fsw_ast, fsw_addr, "FXSAVE FSW operation");
    //         let ftw_expr        = self.symbolicEngine.createSymbolicExpression(inst, aftw_ast, ftw_addr, "FXSAVE Abridged FTW operation");
    //         let fop_expr        = self.symbolicEngine.createSymbolicExpression(inst, fop_ast, fop_addr, "FXSAVE FOP operation");
    //         let fip_expr        = self.symbolicEngine.createSymbolicExpression(inst, fip_ast, fip_addr, "FXSAVE FIP operation");
    //         let fcs_expr        = self.symbolicEngine.createSymbolicExpression(inst, fcs_ast, fcs_addr, "FXSAVE FCS operation");
    //         let fdp_expr        = self.symbolicEngine.createSymbolicExpression(inst, fdp_ast, fdp_addr, "FXSAVE FDP operation");
    //         let fds_expr        = self.symbolicEngine.createSymbolicExpression(inst, fds_ast, fds_addr, "FXSAVE FDS operation");
    //         let mxcsr_expr      = self.symbolicEngine.createSymbolicExpression(inst, mxcsr_ast, mxcsr_addr, "FXSAVE MXCSR operation");
    //         let mxcsr_mask_expr = self.symbolicEngine.createSymbolicExpression(inst, mxcsr_mask_ast, mxcsr_mask_addr, "FXSAVE MXCSR_MASK operation");
    //         let st0_expr        = self.symbolicEngine.createSymbolicExpression(inst, st0_ast, st0_addr, "FXSAVE ST0 operation");
    //         let st1_expr        = self.symbolicEngine.createSymbolicExpression(inst, st1_ast, st1_addr, "FXSAVE ST1 operation");
    //         let st2_expr        = self.symbolicEngine.createSymbolicExpression(inst, st2_ast, st2_addr, "FXSAVE ST2 operation");
    //         let st3_expr        = self.symbolicEngine.createSymbolicExpression(inst, st3_ast, st3_addr, "FXSAVE ST3 operation");
    //         let st4_expr        = self.symbolicEngine.createSymbolicExpression(inst, st4_ast, st4_addr, "FXSAVE ST4 operation");
    //         let st5_expr        = self.symbolicEngine.createSymbolicExpression(inst, st5_ast, st5_addr, "FXSAVE ST5 operation");
    //         let st6_expr        = self.symbolicEngine.createSymbolicExpression(inst, st6_ast, st6_addr, "FXSAVE ST6 operation");
    //         let st7_expr        = self.symbolicEngine.createSymbolicExpression(inst, st7_ast, st7_addr, "FXSAVE ST7 operation");
    //         let xmm0_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm0_ast, xmm0_addr, "FXSAVE XMM0 operation");
    //         let xmm1_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm1_ast, xmm1_addr, "FXSAVE XMM1 operation");
    //         let xmm2_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm2_ast, xmm2_addr, "FXSAVE XMM2 operation");
    //         let xmm3_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm3_ast, xmm3_addr, "FXSAVE XMM3 operation");
    //         let xmm4_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm4_ast, xmm4_addr, "FXSAVE XMM4 operation");
    //         let xmm5_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm5_ast, xmm5_addr, "FXSAVE XMM5 operation");
    //         let xmm6_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm6_ast, xmm6_addr, "FXSAVE XMM6 operation");
    //         let xmm7_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm7_ast, xmm7_addr, "FXSAVE XMM7 operation");

    //         /* Spread the taint */
    //         // fcw_expr.isTainted        = self.taintEngine.taintAssignment(fcw_addr, fcw);
    //         // fsw_expr.isTainted        = self.taintEngine.taintAssignment(fsw_addr, fsw);
    //         // ftw_expr.isTainted        = self.taintEngine.taintAssignment(ftw_addr, ftw);
    //         // fop_expr.isTainted        = self.taintEngine.taintAssignment(fop_addr, fop);
    //         // fip_expr.isTainted        = self.taintEngine.taintAssignment(fip_addr, fip);
    //         // fcs_expr.isTainted        = self.taintEngine.taintAssignment(fcs_addr, fcs);
    //         // fdp_expr.isTainted        = self.taintEngine.taintAssignment(fdp_addr, fdp);
    //         // fds_expr.isTainted        = self.taintEngine.taintAssignment(fds_addr, fds);
    //         // mxcsr_expr.isTainted      = self.taintEngine.taintAssignment(mxcsr_addr, mxcsr);
    //         // mxcsr_mask_expr.isTainted = self.taintEngine.taintAssignment(mxcsr_mask_addr, mxcsr_mask);
    //         // st0_expr.isTainted        = self.taintEngine.taintAssignment(st0_addr, st0);
    //         // st1_expr.isTainted        = self.taintEngine.taintAssignment(st1_addr, st1);
    //         // st2_expr.isTainted        = self.taintEngine.taintAssignment(st2_addr, st2);
    //         // st3_expr.isTainted        = self.taintEngine.taintAssignment(st3_addr, st3);
    //         // st4_expr.isTainted        = self.taintEngine.taintAssignment(st4_addr, st4);
    //         // st5_expr.isTainted        = self.taintEngine.taintAssignment(st5_addr, st5);
    //         // st6_expr.isTainted        = self.taintEngine.taintAssignment(st6_addr, st6);
    //         // st7_expr.isTainted        = self.taintEngine.taintAssignment(st7_addr, st7);
    //         // xmm0_expr.isTainted       = self.taintEngine.taintAssignment(xmm0_addr, xmm0);
    //         // xmm1_expr.isTainted       = self.taintEngine.taintAssignment(xmm1_addr, xmm1);
    //         // xmm2_expr.isTainted       = self.taintEngine.taintAssignment(xmm2_addr, xmm2);
    //         // xmm3_expr.isTainted       = self.taintEngine.taintAssignment(xmm3_addr, xmm3);
    //         // xmm4_expr.isTainted       = self.taintEngine.taintAssignment(xmm4_addr, xmm4);
    //         // xmm5_expr.isTainted       = self.taintEngine.taintAssignment(xmm5_addr, xmm5);
    //         // xmm6_expr.isTainted       = self.taintEngine.taintAssignment(xmm6_addr, xmm6);
    //         // xmm7_expr.isTainted       = self.taintEngine.taintAssignment(xmm7_addr, xmm7);

    //         /* Additional semantics, symbolic expressions and tainting for the '64-bit Mode Layout (with REX.W = 0)' */
    //         if (is64bits) {
    //           let xmm8  = Operand::Register(Register::XMM8);
    //           let xmm9  = Operand::Register(Register::XMM9);
    //           let xmm10 = Operand::Register(Register::XMM10);
    //           let xmm11 = Operand::Register(Register::XMM11);
    //           let xmm12 = Operand::Register(Register::XMM12);
    //           let xmm13 = Operand::Register(Register::XMM13);
    //           let xmm14 = Operand::Register(Register::XMM14);
    //           let xmm15 = Operand::Register(Register::XMM15);

    //           let xmm8_ast  = self.symbolicEngine.getOperandAst(inst, xmm8);
    //           let xmm9_ast  = self.symbolicEngine.getOperandAst(inst, xmm9);
    //           let xmm10_ast = self.symbolicEngine.getOperandAst(inst, xmm10);
    //           let xmm11_ast = self.symbolicEngine.getOperandAst(inst, xmm11);
    //           let xmm12_ast = self.symbolicEngine.getOperandAst(inst, xmm12);
    //           let xmm13_ast = self.symbolicEngine.getOperandAst(inst, xmm13);
    //           let xmm14_ast = self.symbolicEngine.getOperandAst(inst, xmm14);
    //           let xmm15_ast = self.symbolicEngine.getOperandAst(inst, xmm15);

    //           let xmm8_addr  = Operand::Memory(MemoryAccess::new(m512byte + 288, xmm8.getSize()));
    //           let xmm9_addr  = Operand::Memory(MemoryAccess::new(m512byte + 304, xmm9.getSize()));
    //           let xmm10_addr = Operand::Memory(MemoryAccess::new(m512byte + 320, xmm10.getSize()));
    //           let xmm11_addr = Operand::Memory(MemoryAccess::new(m512byte + 336, xmm11.getSize()));
    //           let xmm12_addr = Operand::Memory(MemoryAccess::new(m512byte + 352, xmm12.getSize()));
    //           let xmm13_addr = Operand::Memory(MemoryAccess::new(m512byte + 368, xmm13.getSize()));
    //           let xmm14_addr = Operand::Memory(MemoryAccess::new(m512byte + 384, xmm14.getSize()));
    //           let xmm15_addr = Operand::Memory(MemoryAccess::new(m512byte + 400, xmm15.getSize()));

    //           /* Fetch the original values of the XMM8-XMM15 memory spaces */
    //           let xmm8_orig  = self.symbolicEngine.getOperandAst(xmm8_addr);
    //           let xmm9_orig  = self.symbolicEngine.getOperandAst(xmm9_addr);
    //           let xmm10_orig = self.symbolicEngine.getOperandAst(xmm10_addr);
    //           let xmm11_orig = self.symbolicEngine.getOperandAst(xmm11_addr);
    //           let xmm12_orig = self.symbolicEngine.getOperandAst(xmm12_addr);
    //           let xmm13_orig = self.symbolicEngine.getOperandAst(xmm13_addr);
    //           let xmm14_orig = self.symbolicEngine.getOperandAst(xmm14_addr);
    //           let xmm15_orig = self.symbolicEngine.getOperandAst(xmm15_addr);

    //           /* Check if we are running in CPL = 0 (ring 0) and if the FFXSR bit is set in EFER */
    //           let cpl     = self.ast_ctxt.equal(self.ast_ctxt.extract(1, 0, cs_ast), self.ast_ctxt.bv(0, 2));
    //           let ffx     = self.ast_ctxt.equal(ffxsr_ast, self.ast_ctxt.bv(1, 1));
    //           let is_fast = self.ast_ctxt.land(cpl, ffx);

    //           /* Apply the fast save logic if needed */
    //           xmm8_ast  = self.ast_ctxt.ite(is_fast, xmm8_orig,  xmm8_ast);
    //           xmm9_ast  = self.ast_ctxt.ite(is_fast, xmm9_orig,  xmm9_ast);
    //           xmm10_ast = self.ast_ctxt.ite(is_fast, xmm10_orig, xmm10_ast);
    //           xmm11_ast = self.ast_ctxt.ite(is_fast, xmm11_orig, xmm11_ast);
    //           xmm12_ast = self.ast_ctxt.ite(is_fast, xmm12_orig, xmm12_ast);
    //           xmm13_ast = self.ast_ctxt.ite(is_fast, xmm13_orig, xmm13_ast);
    //           xmm14_ast = self.ast_ctxt.ite(is_fast, xmm14_orig, xmm14_ast);
    //           xmm15_ast = self.ast_ctxt.ite(is_fast, xmm15_orig, xmm15_ast);

    //           let xmm8_expr  = self.symbolicEngine.createSymbolicExpression(inst, xmm8_ast, xmm8_addr, "FXSAVE XMM8 operation");
    //           let xmm9_expr  = self.symbolicEngine.createSymbolicExpression(inst, xmm9_ast, xmm9_addr, "FXSAVE XMM9 operation");
    //           let xmm10_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm10_ast, xmm10_addr, "FXSAVE XMM10 operation");
    //           let xmm11_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm11_ast, xmm11_addr, "FXSAVE XMM11 operation");
    //           let xmm12_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm12_ast, xmm12_addr, "FXSAVE XMM12 operation");
    //           let xmm13_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm13_ast, xmm13_addr, "FXSAVE XMM13 operation");
    //           let xmm14_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm14_ast, xmm14_addr, "FXSAVE XMM14 operation");
    //           let xmm15_expr = self.symbolicEngine.createSymbolicExpression(inst, xmm15_ast, xmm15_addr, "FXSAVE XMM15 operation");

    //         //   xmm8_expr.isTainted  = self.taintEngine.taintAssignment(xmm8_addr, xmm8);
    //         //   xmm9_expr.isTainted  = self.taintEngine.taintAssignment(xmm9_addr, xmm9);
    //         //   xmm10_expr.isTainted = self.taintEngine.taintAssignment(xmm10_addr, xmm10);
    //         //   xmm11_expr.isTainted = self.taintEngine.taintAssignment(xmm11_addr, xmm11);
    //         //   xmm12_expr.isTainted = self.taintEngine.taintAssignment(xmm12_addr, xmm12);
    //         //   xmm13_expr.isTainted = self.taintEngine.taintAssignment(xmm13_addr, xmm13);
    //         //   xmm14_expr.isTainted = self.taintEngine.taintAssignment(xmm14_addr, xmm14);
    //         //   xmm15_expr.isTainted = self.taintEngine.taintAssignment(xmm15_addr, xmm15);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn fxsave64_s(&mut self, inst: x86Instruction) {
    //         /* Fetch the memory operand */
    //         let dst = inst.operands[0];
    //         let mem = dst.getMemory();
    //         let m512byte = mem.getAddress();

    //         /* Check if the address is on a 16-byte boundary */
    //         if (m512byte & 0xF) {
    //         //   self.exception = triton::arch::FAULT_GP;
    //           return;
    //         }

    //         /* Fetch the FPU, STX, SSE, EFER and CS implicit operands */
    //         let fcw        = Operand::Register(Register::FCW);
    //         let fsw        = Operand::Register(Register::FSW);
    //         let ftw        = Operand::Register(Register::FTW);
    //         let fop        = Operand::Register(Register::FOP);
    //         let fip        = Operand::Register(Register::FIP);
    //         let fcs        = Operand::Register(Register::FCS);
    //         let fdp        = Operand::Register(Register::FDP);
    //         let fds        = Operand::Register(Register::FDS);
    //         let mxcsr      = Operand::Register(Register::MXCSR);
    //         let mxcsr_mask = Operand::Register(Register::MXCSR_MASK);
    //         let st0        = Operand::Register(Register::ST0);
    //         let st1        = Operand::Register(Register::ST1);
    //         let st2        = Operand::Register(Register::ST2);
    //         let st3        = Operand::Register(Register::ST3);
    //         let st4        = Operand::Register(Register::ST4);
    //         let st5        = Operand::Register(Register::ST5);
    //         let st6        = Operand::Register(Register::ST6);
    //         let st7        = Operand::Register(Register::ST7);
    //         let xmm0       = Operand::Register(Register::XMM0);
    //         let xmm1       = Operand::Register(Register::XMM1);
    //         let xmm2       = Operand::Register(Register::XMM2);
    //         let xmm3       = Operand::Register(Register::XMM3);
    //         let xmm4       = Operand::Register(Register::XMM4);
    //         let xmm5       = Operand::Register(Register::XMM5);
    //         let xmm6       = Operand::Register(Register::XMM6);
    //         let xmm7       = Operand::Register(Register::XMM7);
    //         let xmm8       = Operand::Register(Register::XMM8);
    //         let xmm9       = Operand::Register(Register::XMM9);
    //         let xmm10      = Operand::Register(Register::XMM10);
    //         let xmm11      = Operand::Register(Register::XMM11);
    //         let xmm12      = Operand::Register(Register::XMM12);
    //         let xmm13      = Operand::Register(Register::XMM13);
    //         let xmm14      = Operand::Register(Register::XMM14);
    //         let xmm15      = Operand::Register(Register::XMM15);
    //         let ffxsr      = Operand::Register(Register::EFER_FFXSR);
    //         let cs         = Operand::Register(Register::CS);

    //         /* Create the symbolic operands */
    //         let fcw_ast        = self.symbolicEngine.getOperandAst(inst, fcw);
    //         let fsw_ast        = self.symbolicEngine.getOperandAst(inst, fsw);
    //         let ftw_ast        = self.symbolicEngine.getOperandAst(inst, ftw);
    //         let fop_ast        = self.symbolicEngine.getOperandAst(inst, fop);
    //         let fip_ast        = self.symbolicEngine.getOperandAst(inst, fip);
    //         let fcs_ast        = self.symbolicEngine.getOperandAst(inst, fcs);
    //         let fdp_ast        = self.symbolicEngine.getOperandAst(inst, fdp);
    //         let fds_ast        = self.symbolicEngine.getOperandAst(inst, fds);
    //         let mxcsr_ast      = self.symbolicEngine.getOperandAst(inst, mxcsr);
    //         let mxcsr_mask_ast = self.symbolicEngine.getOperandAst(inst, mxcsr_mask);
    //         let st0_ast        = self.symbolicEngine.getOperandAst(inst, st0);
    //         let st1_ast        = self.symbolicEngine.getOperandAst(inst, st1);
    //         let st2_ast        = self.symbolicEngine.getOperandAst(inst, st2);
    //         let st3_ast        = self.symbolicEngine.getOperandAst(inst, st3);
    //         let st4_ast        = self.symbolicEngine.getOperandAst(inst, st4);
    //         let st5_ast        = self.symbolicEngine.getOperandAst(inst, st5);
    //         let st6_ast        = self.symbolicEngine.getOperandAst(inst, st6);
    //         let st7_ast        = self.symbolicEngine.getOperandAst(inst, st7);
    //         let xmm0_ast       = self.symbolicEngine.getOperandAst(inst, xmm0);
    //         let xmm1_ast       = self.symbolicEngine.getOperandAst(inst, xmm1);
    //         let xmm2_ast       = self.symbolicEngine.getOperandAst(inst, xmm2);
    //         let xmm3_ast       = self.symbolicEngine.getOperandAst(inst, xmm3);
    //         let xmm4_ast       = self.symbolicEngine.getOperandAst(inst, xmm4);
    //         let xmm5_ast       = self.symbolicEngine.getOperandAst(inst, xmm5);
    //         let xmm6_ast       = self.symbolicEngine.getOperandAst(inst, xmm6);
    //         let xmm7_ast       = self.symbolicEngine.getOperandAst(inst, xmm7);
    //         let xmm8_ast       = self.symbolicEngine.getOperandAst(inst, xmm8);
    //         let xmm9_ast       = self.symbolicEngine.getOperandAst(inst, xmm9);
    //         let xmm10_ast      = self.symbolicEngine.getOperandAst(inst, xmm10);
    //         let xmm11_ast      = self.symbolicEngine.getOperandAst(inst, xmm11);
    //         let xmm12_ast      = self.symbolicEngine.getOperandAst(inst, xmm12);
    //         let xmm13_ast      = self.symbolicEngine.getOperandAst(inst, xmm13);
    //         let xmm14_ast      = self.symbolicEngine.getOperandAst(inst, xmm14);
    //         let xmm15_ast      = self.symbolicEngine.getOperandAst(inst, xmm15);
    //         let ffxsr_ast      = self.symbolicEngine.getOperandAst(inst, ffxsr);
    //         let cs_ast         = self.symbolicEngine.getOperandAst(inst, cs);

    //         /*
    //           Calculate the abridged x87 FPU Tag Word (from 2 bytes to 1 byte encoding)
    //           - Two-bit values of 00, 01, and 10 are encoded as a 1
    //           - A two-bit value of 11 is encoded as a 0
    //         */
    //         let eb_1_0 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(1, 0, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_3_2 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(3, 2, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_5_4 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(5, 4, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_7_6 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(7, 6, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_9_8 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(9, 8, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_11_10 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(11, 10, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_13_12 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(13, 12, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let eb_15_14 = self.ast_ctxt.ite(
    //           self.ast_ctxt.equal(self.ast_ctxt.extract(15, 14, ftw_ast), self.ast_ctxt.bv(3, 2)),
    //           self.ast_ctxt.bv(0, 1), self.ast_ctxt.bv(1, 1));

    //         let aftw_ast = self.ast_ctxt.concat(eb_15_14,
    //           self.ast_ctxt.concat(eb_13_12,
    //           self.ast_ctxt.concat(eb_11_10,
    //           self.ast_ctxt.concat(eb_9_8,
    //           self.ast_ctxt.concat(eb_7_6,
    //           self.ast_ctxt.concat(eb_5_4,
    //           self.ast_ctxt.concat(eb_3_2, eb_1_0)))))));

    //         /* Fetch the implicit memory slots for the '64-bit Mode Layout (with REX.W = 1)' */
    //         let fcw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 0, fcw.getSize()));
    //         let fsw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 2, fsw.getSize()));
    //         let ftw_addr        = Operand::Memory(MemoryAccess::new(m512byte + 4, ftw.getSize() / 2));
    //         let fop_addr        = Operand::Memory(MemoryAccess::new(m512byte + 6, fop.getSize()));
    //         let fip_addr        = Operand::Memory(MemoryAccess::new(m512byte + 8, fip.getSize()));
    //         let fcs_addr        = Operand::Memory(MemoryAccess::new(m512byte + 12, fcs.getSize()));
    //         let fdp_addr        = Operand::Memory(MemoryAccess::new(m512byte + 16, fdp.getSize()));
    //         let fds_addr        = Operand::Memory(MemoryAccess::new(m512byte + 20, fds.getSize()));
    //         let mxcsr_addr      = Operand::Memory(MemoryAccess::new(m512byte + 24, mxcsr.getSize()));
    //         let mxcsr_mask_addr = Operand::Memory(MemoryAccess::new(m512byte + 28, mxcsr_mask.getSize()));
    //         let st0_addr        = Operand::Memory(MemoryAccess::new(m512byte + 32,  st0.getSize()));
    //         let st1_addr        = Operand::Memory(MemoryAccess::new(m512byte + 48,  st1.getSize()));
    //         let st2_addr        = Operand::Memory(MemoryAccess::new(m512byte + 64,  st2.getSize()));
    //         let st3_addr        = Operand::Memory(MemoryAccess::new(m512byte + 80,  st3.getSize()));
    //         let st4_addr        = Operand::Memory(MemoryAccess::new(m512byte + 96,  st4.getSize()));
    //         let st5_addr        = Operand::Memory(MemoryAccess::new(m512byte + 112, st5.getSize()));
    //         let st6_addr        = Operand::Memory(MemoryAccess::new(m512byte + 128, st6.getSize()));
    //         let st7_addr        = Operand::Memory(MemoryAccess::new(m512byte + 144, st7.getSize()));
    //         let xmm0_addr       = Operand::Memory(MemoryAccess::new(m512byte + 160, xmm0.getSize()));
    //         let xmm1_addr       = Operand::Memory(MemoryAccess::new(m512byte + 176, xmm1.getSize()));
    //         let xmm2_addr       = Operand::Memory(MemoryAccess::new(m512byte + 192, xmm2.getSize()));
    //         let xmm3_addr       = Operand::Memory(MemoryAccess::new(m512byte + 208, xmm3.getSize()));
    //         let xmm4_addr       = Operand::Memory(MemoryAccess::new(m512byte + 224, xmm4.getSize()));
    //         let xmm5_addr       = Operand::Memory(MemoryAccess::new(m512byte + 240, xmm5.getSize()));
    //         let xmm6_addr       = Operand::Memory(MemoryAccess::new(m512byte + 256, xmm6.getSize()));
    //         let xmm7_addr       = Operand::Memory(MemoryAccess::new(m512byte + 272, xmm7.getSize()));
    //         let xmm8_addr       = Operand::Memory(MemoryAccess::new(m512byte + 288, xmm8.getSize()));
    //         let xmm9_addr       = Operand::Memory(MemoryAccess::new(m512byte + 304, xmm9.getSize()));
    //         let xmm10_addr      = Operand::Memory(MemoryAccess::new(m512byte + 320, xmm10.getSize()));
    //         let xmm11_addr      = Operand::Memory(MemoryAccess::new(m512byte + 336, xmm11.getSize()));
    //         let xmm12_addr      = Operand::Memory(MemoryAccess::new(m512byte + 352, xmm12.getSize()));
    //         let xmm13_addr      = Operand::Memory(MemoryAccess::new(m512byte + 368, xmm13.getSize()));
    //         let xmm14_addr      = Operand::Memory(MemoryAccess::new(m512byte + 384, xmm14.getSize()));
    //         let xmm15_addr      = Operand::Memory(MemoryAccess::new(m512byte + 400, xmm15.getSize()));

    //         /* Fetch the original values of the XMM0-XMM7 memory spaces */
    //         let xmm0_orig  = self.symbolicEngine.getOperandAst(xmm0_addr);
    //         let xmm1_orig  = self.symbolicEngine.getOperandAst(xmm1_addr);
    //         let xmm2_orig  = self.symbolicEngine.getOperandAst(xmm2_addr);
    //         let xmm3_orig  = self.symbolicEngine.getOperandAst(xmm3_addr);
    //         let xmm4_orig  = self.symbolicEngine.getOperandAst(xmm4_addr);
    //         let xmm5_orig  = self.symbolicEngine.getOperandAst(xmm5_addr);
    //         let xmm6_orig  = self.symbolicEngine.getOperandAst(xmm6_addr);
    //         let xmm7_orig  = self.symbolicEngine.getOperandAst(xmm7_addr);
    //         let xmm8_orig  = self.symbolicEngine.getOperandAst(xmm8_addr);
    //         let xmm9_orig  = self.symbolicEngine.getOperandAst(xmm9_addr);
    //         let xmm10_orig = self.symbolicEngine.getOperandAst(xmm10_addr);
    //         let xmm11_orig = self.symbolicEngine.getOperandAst(xmm11_addr);
    //         let xmm12_orig = self.symbolicEngine.getOperandAst(xmm12_addr);
    //         let xmm13_orig = self.symbolicEngine.getOperandAst(xmm13_addr);
    //         let xmm14_orig = self.symbolicEngine.getOperandAst(xmm14_addr);
    //         let xmm15_orig = self.symbolicEngine.getOperandAst(xmm15_addr);

    //         /* Check if we are running in CPL = 0 (ring 0) and if the FFXSR bit is set in EFER */
    //         let cpl     = self.ast_ctxt.equal(self.ast_ctxt.extract(1, 0, cs_ast), self.ast_ctxt.bv(0, 2));
    //         let ffx     = self.ast_ctxt.equal(ffxsr_ast, self.ast_ctxt.bv(1, 1));
    //         let is_fast = self.ast_ctxt.land(cpl, ffx);

    //         /* Apply the fast save logic if needed */
    //         xmm0_ast  = self.ast_ctxt.ite(is_fast, xmm0_orig,  xmm0_ast);
    //         xmm1_ast  = self.ast_ctxt.ite(is_fast, xmm1_orig,  xmm1_ast);
    //         xmm2_ast  = self.ast_ctxt.ite(is_fast, xmm2_orig,  xmm2_ast);
    //         xmm3_ast  = self.ast_ctxt.ite(is_fast, xmm3_orig,  xmm3_ast);
    //         xmm4_ast  = self.ast_ctxt.ite(is_fast, xmm4_orig,  xmm4_ast);
    //         xmm5_ast  = self.ast_ctxt.ite(is_fast, xmm5_orig,  xmm5_ast);
    //         xmm6_ast  = self.ast_ctxt.ite(is_fast, xmm6_orig,  xmm6_ast);
    //         xmm7_ast  = self.ast_ctxt.ite(is_fast, xmm7_orig,  xmm7_ast);
    //         xmm8_ast  = self.ast_ctxt.ite(is_fast, xmm8_orig,  xmm8_ast);
    //         xmm9_ast  = self.ast_ctxt.ite(is_fast, xmm9_orig,  xmm9_ast);
    //         xmm10_ast = self.ast_ctxt.ite(is_fast, xmm10_orig, xmm10_ast);
    //         xmm11_ast = self.ast_ctxt.ite(is_fast, xmm11_orig, xmm11_ast);
    //         xmm12_ast = self.ast_ctxt.ite(is_fast, xmm12_orig, xmm12_ast);
    //         xmm13_ast = self.ast_ctxt.ite(is_fast, xmm13_orig, xmm13_ast);
    //         xmm14_ast = self.ast_ctxt.ite(is_fast, xmm14_orig, xmm14_ast);
    //         xmm15_ast = self.ast_ctxt.ite(is_fast, xmm15_orig, xmm15_ast);

    //         /* Craft the symbolic expressions */
    //         let fcw_expr        = self.symbolicEngine.createSymbolicExpression(inst, fcw_ast, fcw_addr, "FXSAVE64 FCW operation");
    //         let fsw_expr        = self.symbolicEngine.createSymbolicExpression(inst, fsw_ast, fsw_addr, "FXSAVE64 FSW operation");
    //         let ftw_expr        = self.symbolicEngine.createSymbolicExpression(inst, aftw_ast, ftw_addr, "FXSAVE64 Abridged FTW operation");
    //         let fop_expr        = self.symbolicEngine.createSymbolicExpression(inst, fop_ast, fop_addr, "FXSAVE64 FOP operation");
    //         let fip_expr        = self.symbolicEngine.createSymbolicExpression(inst, fip_ast, fip_addr, "FXSAVE64 FIP operation");
    //         let fcs_expr        = self.symbolicEngine.createSymbolicExpression(inst, fcs_ast, fcs_addr, "FXSAVE64 FCS operation");
    //         let fdp_expr        = self.symbolicEngine.createSymbolicExpression(inst, fdp_ast, fdp_addr, "FXSAVE64 FDP operation");
    //         let fds_expr        = self.symbolicEngine.createSymbolicExpression(inst, fds_ast, fds_addr, "FXSAVE64 FDS operation");
    //         let mxcsr_expr      = self.symbolicEngine.createSymbolicExpression(inst, mxcsr_ast, mxcsr_addr, "FXSAVE64 MXCSR operation");
    //         let mxcsr_mask_expr = self.symbolicEngine.createSymbolicExpression(inst, mxcsr_mask_ast, mxcsr_mask_addr, "FXSAVE64 MXCSR_MASK operation");
    //         let st0_expr        = self.symbolicEngine.createSymbolicExpression(inst, st0_ast, st0_addr, "FXSAVE64 ST0 operation");
    //         let st1_expr        = self.symbolicEngine.createSymbolicExpression(inst, st1_ast, st1_addr, "FXSAVE64 ST1 operation");
    //         let st2_expr        = self.symbolicEngine.createSymbolicExpression(inst, st2_ast, st2_addr, "FXSAVE64 ST2 operation");
    //         let st3_expr        = self.symbolicEngine.createSymbolicExpression(inst, st3_ast, st3_addr, "FXSAVE64 ST3 operation");
    //         let st4_expr        = self.symbolicEngine.createSymbolicExpression(inst, st4_ast, st4_addr, "FXSAVE64 ST4 operation");
    //         let st5_expr        = self.symbolicEngine.createSymbolicExpression(inst, st5_ast, st5_addr, "FXSAVE64 ST5 operation");
    //         let st6_expr        = self.symbolicEngine.createSymbolicExpression(inst, st6_ast, st6_addr, "FXSAVE64 ST6 operation");
    //         let st7_expr        = self.symbolicEngine.createSymbolicExpression(inst, st7_ast, st7_addr, "FXSAVE64 ST7 operation");
    //         let xmm0_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm0_ast, xmm0_addr, "FXSAVE64 XMM0 operation");
    //         let xmm1_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm1_ast, xmm1_addr, "FXSAVE64 XMM1 operation");
    //         let xmm2_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm2_ast, xmm2_addr, "FXSAVE64 XMM2 operation");
    //         let xmm3_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm3_ast, xmm3_addr, "FXSAVE64 XMM3 operation");
    //         let xmm4_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm4_ast, xmm4_addr, "FXSAVE64 XMM4 operation");
    //         let xmm5_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm5_ast, xmm5_addr, "FXSAVE64 XMM5 operation");
    //         let xmm6_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm6_ast, xmm6_addr, "FXSAVE64 XMM6 operation");
    //         let xmm7_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm7_ast, xmm7_addr, "FXSAVE64 XMM7 operation");
    //         let xmm8_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm8_ast, xmm8_addr, "FXSAVE64 XMM8 operation");
    //         let xmm9_expr       = self.symbolicEngine.createSymbolicExpression(inst, xmm9_ast, xmm9_addr, "FXSAVE64 XMM9 operation");
    //         let xmm10_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm10_ast, xmm10_addr, "FXSAVE64 XMM10 operation");
    //         let xmm11_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm11_ast, xmm11_addr, "FXSAVE64 XMM11 operation");
    //         let xmm12_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm12_ast, xmm12_addr, "FXSAVE64 XMM12 operation");
    //         let xmm13_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm13_ast, xmm13_addr, "FXSAVE64 XMM13 operation");
    //         let xmm14_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm14_ast, xmm14_addr, "FXSAVE64 XMM14 operation");
    //         let xmm15_expr      = self.symbolicEngine.createSymbolicExpression(inst, xmm15_ast, xmm15_addr, "FXSAVE64 XMM15 operation");

    //         /* Spread the taint */
    //         // fcw_expr.isTainted        = self.taintEngine.taintAssignment(fcw_addr, fcw);
    //         // fsw_expr.isTainted        = self.taintEngine.taintAssignment(fsw_addr, fsw);
    //         // ftw_expr.isTainted        = self.taintEngine.taintAssignment(ftw_addr, ftw);
    //         // fop_expr.isTainted        = self.taintEngine.taintAssignment(fop_addr, fop);
    //         // fip_expr.isTainted        = self.taintEngine.taintAssignment(fip_addr, fip);
    //         // fcs_expr.isTainted        = self.taintEngine.taintAssignment(fcs_addr, fcs);
    //         // fdp_expr.isTainted        = self.taintEngine.taintAssignment(fdp_addr, fdp);
    //         // fds_expr.isTainted        = self.taintEngine.taintAssignment(fds_addr, fds);
    //         // mxcsr_expr.isTainted      = self.taintEngine.taintAssignment(mxcsr_addr, mxcsr);
    //         // mxcsr_mask_expr.isTainted = self.taintEngine.taintAssignment(mxcsr_mask_addr, mxcsr_mask);
    //         // st0_expr.isTainted        = self.taintEngine.taintAssignment(st0_addr, st0);
    //         // st1_expr.isTainted        = self.taintEngine.taintAssignment(st1_addr, st1);
    //         // st2_expr.isTainted        = self.taintEngine.taintAssignment(st2_addr, st2);
    //         // st3_expr.isTainted        = self.taintEngine.taintAssignment(st3_addr, st3);
    //         // st4_expr.isTainted        = self.taintEngine.taintAssignment(st4_addr, st4);
    //         // st5_expr.isTainted        = self.taintEngine.taintAssignment(st5_addr, st5);
    //         // st6_expr.isTainted        = self.taintEngine.taintAssignment(st6_addr, st6);
    //         // st7_expr.isTainted        = self.taintEngine.taintAssignment(st7_addr, st7);
    //         // xmm0_expr.isTainted       = self.taintEngine.taintAssignment(xmm0_addr, xmm0);
    //         // xmm1_expr.isTainted       = self.taintEngine.taintAssignment(xmm1_addr, xmm1);
    //         // xmm2_expr.isTainted       = self.taintEngine.taintAssignment(xmm2_addr, xmm2);
    //         // xmm3_expr.isTainted       = self.taintEngine.taintAssignment(xmm3_addr, xmm3);
    //         // xmm4_expr.isTainted       = self.taintEngine.taintAssignment(xmm4_addr, xmm4);
    //         // xmm5_expr.isTainted       = self.taintEngine.taintAssignment(xmm5_addr, xmm5);
    //         // xmm6_expr.isTainted       = self.taintEngine.taintAssignment(xmm6_addr, xmm6);
    //         // xmm7_expr.isTainted       = self.taintEngine.taintAssignment(xmm7_addr, xmm7);
    //         // xmm8_expr.isTainted       = self.taintEngine.taintAssignment(xmm8_addr, xmm8);
    //         // xmm9_expr.isTainted       = self.taintEngine.taintAssignment(xmm9_addr, xmm9);
    //         // xmm10_expr.isTainted      = self.taintEngine.taintAssignment(xmm10_addr, xmm10);
    //         // xmm11_expr.isTainted      = self.taintEngine.taintAssignment(xmm11_addr, xmm11);
    //         // xmm12_expr.isTainted      = self.taintEngine.taintAssignment(xmm12_addr, xmm12);
    //         // xmm13_expr.isTainted      = self.taintEngine.taintAssignment(xmm13_addr, xmm13);
    //         // xmm14_expr.isTainted      = self.taintEngine.taintAssignment(xmm14_addr, xmm14);
    //         // xmm15_expr.isTainted      = self.taintEngine.taintAssignment(xmm15_addr, xmm15);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn idiv_s(&mut self, inst: x86Instruction) {
    //         let src = inst.operands[0];

    //         /* Create symbolic operands */
    //         let divisor = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         match src.getSize() {

    //           ByteSizes::BYTE => {
    //             /* AX */
    //             let ax = Operand::Register(Register::AX);
    //             let dividend = self.symbolicEngine.getOperandAst(inst, ax);
    //             /* res = AX / Source */
    //             let result = self.ast_ctxt.bvsdiv(dividend, self.ast_ctxt.sx(BitSizes::BYTE, divisor));
    //             /* mod_ = AX % Source */
    //             let mod_ = self.ast_ctxt.bvsmod(dividend, self.ast_ctxt.sx(BitSizes::BYTE, divisor));
    //             /* AH = mod_ */
    //             /* AL = res */
    //             let node = self.ast_ctxt.concat(
    //                           self.ast_ctxt.extract((BitSizes::BYTE - 1), 0, mod_),   /* AH = mod_ */
    //                           self.ast_ctxt.extract((BitSizes::BYTE - 1), 0, result) /* AL = res */
    //                         );
    //             /* Create symbolic expression */
    //             let expr = self.symbolicEngine.createSymbolicExpression(inst, node, ax, "IDIV operation");
    //             /* Apply the taint */
    //             // expr.isTainted = self.taintEngine.taintUnion(ax, src);
    //           }

    //           ByteSizes::WORD => {
    //             /* DX:AX */
    //             let dx = Operand::Register(Register::DX);
    //             let ax = Operand::Register(Register::AX);
    //             let dividend = self.ast_ctxt.concat(self.symbolicEngine.getOperandAst(inst, dx), self.symbolicEngine.getOperandAst(inst, ax));
    //             /* res = DX:AX / Source */
    //             let temp = self.ast_ctxt.bvsdiv(dividend, self.ast_ctxt.sx(BitSizes::WORD, divisor));
    //             let result = self.ast_ctxt.extract((BitSizes::WORD - 1), 0, temp);
    //             /* mod_ = DX:AX % Source */
    //             let mod_ = self.ast_ctxt.extract((BitSizes::WORD - 1), 0, self.ast_ctxt.bvsmod(dividend, self.ast_ctxt.sx(BitSizes::WORD, divisor)));
    //             /* Create the symbolic expression for AX */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, result, ax, "IDIV operation");
    //             /* Apply the taint for AX */
    //             // expr1.isTainted = self.taintEngine.taintUnion(ax, src);
    //             /* Create the symbolic expression for DX */
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, mod_, dx, "IDIV operation");
    //             /* Apply the taint for DX */
    //             // expr2.isTainted = self.taintEngine.taintUnion(dx, src);
    //           }

    //           ByteSizes::DWORD => {
    //             /* EDX:EAX */
    //             let edx = Operand::Register(Register::EDX);
    //             let eax = Operand::Register(Register::EAX);
    //             let dividend = self.ast_ctxt.concat(self.symbolicEngine.getOperandAst(inst, edx), self.symbolicEngine.getOperandAst(inst, eax));
    //             /* res = EDX:EAX / Source */
    //             let temp = self.ast_ctxt.bvsdiv(dividend, self.ast_ctxt.sx(BitSizes::DWORD, divisor));
    //             let result = self.ast_ctxt.extract((BitSizes::DWORD - 1), 0, temp);
    //             /* mod_ = EDX:EAX % Source */
    //             let mod_ = self.ast_ctxt.extract((BitSizes::DWORD - 1), 0, self.ast_ctxt.bvsmod(dividend, self.ast_ctxt.sx(BitSizes::DWORD, divisor)));
    //             /* Create the symbolic expression for EAX */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, result, eax, "IDIV operation");
    //             /* Apply the taint for EAX */
    //             // expr1.isTainted = self.taintEngine.taintUnion(eax, src);
    //             /* Create the symbolic expression for EDX */
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, mod_, edx, "IDIV operation");
    //             /* Apply the taint for EDX */
    //             // expr2.isTainted = self.taintEngine.taintUnion(edx, src);
    //           }

    //           ByteSizes::QWORD => {
    //             /* RDX:RAX */
    //             let rdx = Operand::Register(Register::RDX);
    //             let rax = Operand::Register(Register::RAX);
    //             let dividend = self.ast_ctxt.concat(self.symbolicEngine.getOperandAst(inst, rdx), self.symbolicEngine.getOperandAst(inst, rax));
    //             /* res = RDX:RAX / Source */
    //             let temp = self.ast_ctxt.bvsdiv(dividend, self.ast_ctxt.sx(BitSizes::QWORD, divisor));
    //             let result = self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, temp);
    //             /* mod_ = RDX:RAX % Source */
    //             let mod_ = self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, self.ast_ctxt.bvsmod(dividend, self.ast_ctxt.sx(BitSizes::QWORD, divisor)));
    //             /* Create the symbolic expression for RAX */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, result, rax, "IDIV operation");
    //             /* Apply the taint for EAX */
    //             // expr1.isTainted = self.taintEngine.taintUnion(rax, src);
    //             /* Create the symbolic expression for RDX */
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, mod_, rdx, "IDIV operation");
    //             /* Apply the taint for EDX */
    //             // expr2.isTainted = self.taintEngine.taintUnion(rdx, src);
    //           }

    //         }

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::CF);
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);
    //         self.undefined_s(inst, Register::ZF);

    //         /* Return an exception if the divisor is zero */
    //         if (divisor.evaluate() == 0) {
    //         //   self.exception = triton::arch::FAULT_DE;
    //           return;
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn imul_s(&mut self, inst: x86Instruction) {
    //         match inst.op_count() {

    //           /* one operand */
    //           1 => {
    //             let src = inst.operands[0];

    //             /* size of the Operand */
    //             match src.getSize() {

    //               /* dst = AX */
    //               ByteSizes::BYTE => {
    //                 let ax   = Operand::Register(Register::AX);
    //                 let al   = Operand::Register(Register::AL);
    //                 let op1  = self.symbolicEngine.getOperandAst(inst, al);
    //                 let op2  = self.symbolicEngine.getOperandAst(inst, src);
    //                 let node = self.ast_ctxt.bvmul(self.ast_ctxt.sx(BitSizes::BYTE, op1), self.ast_ctxt.sx(BitSizes::BYTE, op2));
    //                 let expr = self.symbolicEngine.createSymbolicExpression(inst, node, ax, "IMUL operation");
    //                 // expr.isTainted = self.taintEngine.taintUnion(ax, src);
    //                 self.cfImul_s(inst, expr, al, self.ast_ctxt.bvmul(op1, op2), node);
    //                 self.ofImul_s(inst, expr, al, self.ast_ctxt.bvmul(op1, op2), node);
    //               }

    //               /* dst = DX:AX */
    //               ByteSizes::WORD => {
    //                 let ax    = Operand::Register(Register::AX);
    //                 let dx    = Operand::Register(Register::DX);
    //                 let op1   = self.symbolicEngine.getOperandAst(inst, ax);
    //                 let op2   = self.symbolicEngine.getOperandAst(inst, src);
    //                 let node1 = self.ast_ctxt.bvmul(op1, op2);
    //                 let node2 = self.ast_ctxt.bvmul(self.ast_ctxt.sx(BitSizes::WORD, op1), self.ast_ctxt.sx(BitSizes::WORD, op2));
    //                 let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, ax, "IMUL operation");
    //                 let expr2 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract(BitSizes::DWORD-1, BitSizes::WORD, node2), dx, "IMUL operation");
    //                 // expr1.isTainted = self.taintEngine.taintUnion(ax, src);
    //                 // expr2.isTainted = self.taintEngine.taintUnion(dx, ax);
    //                 self.cfImul_s(inst, expr1, ax, node1, node2);
    //                 self.ofImul_s(inst, expr1, ax, node1, node2);
    //               }

    //               /* dst = EDX:EAX */
    //               ByteSizes::DWORD => {
    //                 let eax   = Operand::Register(Register::EAX);
    //                 let edx   = Operand::Register(Register::EDX);
    //                 let op1   = self.symbolicEngine.getOperandAst(inst, eax);
    //                 let op2   = self.symbolicEngine.getOperandAst(inst, src);
    //                 let node1 = self.ast_ctxt.bvmul(op1, op2);
    //                 let node2 = self.ast_ctxt.bvmul(self.ast_ctxt.sx(BitSizes::DWORD, op1), self.ast_ctxt.sx(BitSizes::DWORD, op2));
    //                 let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, eax, "IMUL operation");
    //                 let expr2 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract(BitSizes::QWORD-1, BitSizes::DWORD, node2), edx, "IMUL operation");
    //                 // expr1.isTainted = self.taintEngine.taintUnion(eax, src);
    //                 // expr2.isTainted = self.taintEngine.taintUnion(edx, eax);
    //                 self.cfImul_s(inst, expr1, eax, node1, node2);
    //                 self.ofImul_s(inst, expr1, eax, node1, node2);
    //               }

    //               /* dst = RDX:RAX */
    //               ByteSizes::QWORD => {
    //                 let rax   = Operand::Register(Register::RAX);
    //                 let rdx   = Operand::Register(Register::RDX);
    //                 let op1   = self.symbolicEngine.getOperandAst(inst, rax);
    //                 let op2   = self.symbolicEngine.getOperandAst(inst, src);
    //                 let node1 = self.ast_ctxt.bvmul(op1, op2);
    //                 let node2 = self.ast_ctxt.bvmul(self.ast_ctxt.sx(BitSizes::QWORD, op1), self.ast_ctxt.sx(BitSizes::QWORD, op2));
    //                 let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, rax, "IMUL operation");
    //                 let expr2 = self.symbolicEngine.createSymbolicExpression(inst, self.ast_ctxt.extract(BitSizes::DQWORD-1, BitSizes::QWORD, node2), rdx, "IMUL operation");
    //                 // expr1.isTainted = self.taintEngine.taintUnion(rax, src);
    //                 // expr2.isTainted = self.taintEngine.taintUnion(rdx, rax);
    //                 self.cfImul_s(inst, expr1, rax, node1, node2);
    //                 self.ofImul_s(inst, expr1, rax, node1, node2);
    //               }

    //             }
    //           }

    //           /* two operands */
    //           2 => {
    //             let dst   = inst.operands[0];
    //             let src   = inst.operands[1];
    //             let  op1   = self.symbolicEngine.getOperandAst(inst, dst);
    //             let  op2   = self.symbolicEngine.getOperandAst(inst, src);
    //             let  node1 = self.ast_ctxt.bvmul(op1, op2);
    //             let  node2 = self.ast_ctxt.bvmul(self.ast_ctxt.sx(dst.get_bit_size(), op1), self.ast_ctxt.sx(src.get_bit_size(), op2));
    //             let  expr  = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "IMUL operation");
    //             // expr.isTainted = self.taintEngine.taintUnion(dst, src);
    //             self.cfImul_s(inst, expr, dst, node1, node2);
    //             self.ofImul_s(inst, expr, dst, node1, node2);
    //           }

    //           /* three operands */
    //           3 => {
    //             let dst   = inst.operands[0];
    //             let src1  = inst.operands[1];
    //             let src2  = inst.operands[2];
    //             let  op2   = self.symbolicEngine.getOperandAst(inst, src1);
    //             let  op3   = self.ast_ctxt.sx(src1.get_bit_size() - src2.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src2));
    //             let  node1 = self.ast_ctxt.bvmul(op2, op3);
    //             let  node2 = self.ast_ctxt.bvmul(self.ast_ctxt.sx(src1.get_bit_size(), op2), self.ast_ctxt.sx(src2.get_bit_size(), op3));
    //             let  expr  = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "IMUL operation");
    //             // // // expr.isTainted = self.taintEngine.setTaint(dst, self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2));
    //             self.cfImul_s(inst, expr, dst, node1, node2);
    //             self.ofImul_s(inst, expr, dst, node1, node2);
    //           }
    //           _ => unreachable!(),

    //         }

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);
    //         self.undefined_s(inst, Register::ZF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn inc_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.bv(1, dst.get_bit_size());

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvadd(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "INC operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, dst);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr, dst, op1, op2);
    //         self.ofAdd_s(inst, expr, dst, op1, op2);
    //         self.pf_s(inst, expr, dst);
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn invd_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn invlpg_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn ja_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  cf      = Operand::Register(Register::CF);
    //         let  zf      = Operand::Register(Register::ZF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, cf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, zf);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.bvand(
    //                           self.ast_ctxt.bvnot(op1),
    //                           self.ast_ctxt.bvnot(op2)
    //                         ),
    //                         self.ast_ctxt.bvtrue()
    //                       ), op4, op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op1.evaluate().is_zero() && op2.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, cf);
    //         // expr.isTainted = self.taintEngine.taintUnion(pc, zf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jae_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  cf      = Operand::Register(Register::CF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, cf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvfalse()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, cf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jb_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  cf      = Operand::Register(Register::CF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, cf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvtrue()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, cf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jbe_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  cf      = Operand::Register(Register::CF);
    //         let  zf      = Operand::Register(Register::ZF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, cf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, zf);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvor(op1, op2), self.ast_ctxt.bvtrue()), op4, op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero() || !op2.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, cf);
    //         // expr.isTainted = self.taintEngine.taintUnion(pc, zf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jcxz_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  cx      = Operand::Register(Register::CX);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, cx);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, BitSizes::WORD)), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, cx);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn je_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  zf      = Operand::Register(Register::ZF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, zf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvtrue()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, zf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jecxz_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  ecx     = Operand::Register(Register::ECX);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, ecx);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, BitSizes::DWORD)), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, ecx);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jg_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  sf      = Operand::Register(Register::SF);
    //         let  of      = Operand::Register(Register::OF);
    //         let  zf      = Operand::Register(Register::ZF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, zf);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvor(self.ast_ctxt.bvxor(op1, op2), op3), self.ast_ctxt.bvfalse()), op5, op4);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if ((op1.evaluate().is_zero() == op2.evaluate().is_zero()) && op3.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, sf);
    //         // expr.isTainted = self.taintEngine.taintUnion(pc, of);
    //         // expr.isTainted = self.taintEngine.taintUnion(pc, zf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jge_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  sf      = Operand::Register(Register::SF);
    //         let  of      = Operand::Register(Register::OF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, op2), op4, op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op1.evaluate().is_zero() == op2.evaluate().is_zero()){
    //           inst.setConditionTaken(true);}

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, sf);
    //         // expr.isTainted = self.taintEngine.taintUnion(pc, of);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jl_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  sf      = Operand::Register(Register::SF);
    //         let  of      = Operand::Register(Register::OF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvxor(op1, op2), self.ast_ctxt.bvtrue()), op4, op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op1.evaluate().is_zero() != op2.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, sf);
    //         // expr.isTainted = self.taintEngine.taintUnion(pc, of);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jle_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  sf      = Operand::Register(Register::SF);
    //         let  of      = Operand::Register(Register::OF);
    //         let  zf      = Operand::Register(Register::ZF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, zf);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.bvor(self.ast_ctxt.bvxor(op1, op2), op3), self.ast_ctxt.bvtrue()), op5, op4);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if ((op1.evaluate().is_zero() != op2.evaluate().is_zero()) || !op3.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, sf);
    //         // expr.isTainted = self.taintEngine.taintUnion(pc, of);
    //         // expr.isTainted = self.taintEngine.taintUnion(pc, zf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jmp_s(&mut self, inst: x86Instruction) {
    //         let  pc  = Operand::Register(self.architecture.get_program_counter());
    //         let src = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = op1;

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         inst.setConditionTaken(true);

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, src);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jne_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  zf      = Operand::Register(Register::ZF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, zf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvfalse()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, zf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jno_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  of      = Operand::Register(Register::OF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvfalse()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, of);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jnp_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  pf      = Operand::Register(Register::PF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, pf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvfalse()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, pf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jns_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  sf      = Operand::Register(Register::SF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvfalse()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, sf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jo_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  of      = Operand::Register(Register::OF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvtrue()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, of);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jp_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  pf      = Operand::Register(Register::PF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, pf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvtrue()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, pf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn jrcxz_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  rcx     = Operand::Register(Register::RCX);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, rcx);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, BitSizes::QWORD)), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, rcx);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn js_s(&mut self, inst: x86Instruction) {
    //         let  pc      = Operand::Register(self.architecture.get_program_counter());
    //         let  sf      = Operand::Register(Register::SF);
    //         let  srcImm1 = Operand::Imm(inst.next_ip(), pc.getSize());
    //         let srcImm2 = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, srcImm1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, srcImm2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(self.ast_ctxt.equal(op1, self.ast_ctxt.bvtrue()), op3, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (!op1.evaluate().is_zero()){
    //           inst.setConditionTaken(true);
    // }
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, sf);

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn lahf_s(&mut self, inst: x86Instruction) {
    //         let dst  = Operand::Register(Register::AH);
    //         let src1 = Operand::Register(Register::SF);
    //         let src2 = Operand::Register(Register::ZF);
    //         let src3 = Operand::Register(Register::AF);
    //         let src4 = Operand::Register(Register::PF);
    //         let src5 = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src3);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, src4);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, src5);

    //         /* Create the semantics */
    //         let mut flags: Vec<Instruction> = Vec::new();
    //         flags.reserve(8);

    //         flags.push(op1);
    //         flags.push(op2);
    //         flags.push(self.ast_ctxt.bvfalse());
    //         flags.push(op3);
    //         flags.push(self.ast_ctxt.bvfalse());
    //         flags.push(op4);
    //         flags.push(self.ast_ctxt.bvtrue());
    //         flags.push(op5);

    //         let node = self.ast_ctxt.concat(flags);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "LAHF operation");

    //         /* Spread taint */
    //         // self.taintEngine.taintUnion(dst, src1);
    //         // self.taintEngine.taintUnion(dst, src2);
    //         // self.taintEngine.taintUnion(dst, src3);
    //         // self.taintEngine.taintUnion(dst, src4);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src5);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn lddqu_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "LDDQU operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn ldmxcsr_s(&mut self, inst: x86Instruction) {
    //         let  dst = Operand::Register(Register::MXCSR);
    //         let src = inst.operands[0];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "LDMXCSR operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    fn lea_s(&mut self, inst: x86Instruction) {
        let dst = inst.op0_register();
        let src_disp = inst.memory_displacement64();
        let src_disp_bit_size = inst.memory_displ_size() * 8;
        let src_base = inst.memory_base();
        let src_index = inst.memory_index();
        let src_scale = inst.memory_index_scale();
        // let dst                = inst.operands[0].getRegister();
        // let src_disp            = inst.operands[1].getMemory().getDisplacement();
        // let src_base            = inst.operands[1].getMemory().getBaseRegister();
        // let src_index           = inst.operands[1].getMemory().getIndexRegister();
        // let src_scale           = inst.operands[1].getMemory().getScale();
        let mut lea_size: u32 = 0;

        /* Setup LEA size */
        if (self.architecture.is_register_valid(src_base)) {
            lea_size = src_base.size() as u32 * 8;
        } else if (self.architecture.is_register_valid(src_index)) {
            lea_size = src_index.size() as u32 * 8;
        } else {
            lea_size = src_disp_bit_size;
        }
        /* Create symbolic operands */
        /* Displacement */
        let mut op2 = Operand::Imm(src_disp, 64);
        if (lea_size > src_disp_bit_size) {
            op2 = Operand::Instruction(self.ast_ctxt.zx(lea_size - src_disp_bit_size, op2));
        }
        /* Base */
        let mut op3 = if (self.architecture.is_register_valid(src_base)) {
            Operand::Register(src_base)
        } else {
            Operand::Instruction(self.ast_ctxt.bv(0, lea_size))
        };
        /* Base with PC */
        if (self.architecture.is_register_valid(src_base)
            && (src_base.full_register() == self.architecture.get_program_counter()))
        {
            op3 = Operand::Instruction(self.ast_ctxt.bvadd(
                op3,
                // todo: perhaps it actually wants inst.size()
                Operand::Instruction(self.ast_ctxt.bv(inst.len() as u64, lea_size)),
            ));
        }
        /* Index */
        let mut op4 = if (self.architecture.is_register_valid(src_index)) {
            Operand::Register(src_index)
        } else {
            Operand::Instruction(self.ast_ctxt.bv(0, lea_size))
        };
        /* Scale */
        let mut op5 = Operand::Imm(src_scale as u64, 32);
        if (lea_size > 32) {
            op5 = Operand::Instruction(self.ast_ctxt.zx(lea_size - 32, op5));
        }
        /* Create the semantics */
        /* Effective address = Displacement + BaseReg + IndexReg * Scale */
        let mut node = Operand::Instruction(
            self.ast_ctxt.bvadd(
                op2,
                Operand::Instruction(
                    self.ast_ctxt
                        .bvadd(op3, Operand::Instruction(self.ast_ctxt.bvmul(op4, op5))),
                ),
            ),
        );

        let dst_bit_size = dst.size() as u32 * 8;
        let dst = OperandWrapper(inst, 0);

        if (dst_bit_size > lea_size) {
            node = Operand::Instruction(self.ast_ctxt.zx(dst_bit_size - lea_size, node));
        }
        if (dst_bit_size < lea_size) {
            node = Operand::Instruction(self.ast_ctxt.extract(dst.get_high(), dst.get_low(), node));
        }
        /* Create symbolic expression */
        // let expr = self.symbolicEngine.createSymbolicRegisterExpression(inst, node, dst, "LEA operation");

        /* Spread taint */
        // // // expr.isTainted = self.taintEngine.setTaint(dst, self.taintEngine.isTainted(src_base) | self.taintEngine.isTainted(src_index));

        /* Update the symbolic control flow */
        // self.controlFlow_s(inst);
    }

    //       fn leave_s(&mut self, inst: x86Instruction) {
    //         let stack     = self.architecture.get_stack_pointer();
    //         let base      = Register::BP.full_register();
    //         let baseValue = self.architecture.getConcreteRegisterValue(base) as u64;
    //         let bp1       = Operand::Memory(MemoryAccess::new(baseValue, base.getSize()));
    //         let bp2       = Operand::Register(Register::BP.full_register());
    //         let sp        = Operand::Register(stack);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, bp2);

    //         /* RSP = RBP */
    //         let node1 = op1;

    //         /* Create the symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, sp, "Stack Pointer");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(sp, bp2);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, bp1);

    //         /* RBP = pop() */
    //         let node2 = op2;

    //         /* Create the symbolic expression */
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, bp2, "Stack Top Pointer");

    //         /* Spread taint */
    //         // expr2.isTainted = self.taintEngine.taintAssignment(bp2, bp1);

    //         /* Create the semantics - side effect */
    //         alignAddStack_s(inst, bp1.getSize());

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn lfence_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn lodsb_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::SI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::BYTE, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::BYTE, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "LODSB operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn lodsd_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::SI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::DWORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::DWORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "LODSD operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn lodsq_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::SI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::QWORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::QWORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "LODSQ operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn lodsw_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::SI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::WORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::WORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "LODSW operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn loop_s(&mut self, inst: x86Instruction) {
    //         let  count = Operand::Register(Register::CX.full_register());
    //         let  pc    = Operand::Register(self.architecture.get_program_counter());
    //         let src   = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, count);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op2, self.ast_ctxt.bv(0, op2.getBitvectorSize())),
    //                        self.ast_ctxt.bv(inst.next_ip(), pc.get_bit_size()),
    //                        op1
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, pc, "Program Counter");

    //         /* Set condition flag */
    //         if (op2.evaluate()) {
    //           inst.setConditionTaken(true);
    //           /* Spread taint */
    //         //   expr1.isTainted = self.taintEngine.taintAssignment(pc, count);
    //         }
    //         else {
    //         //   expr1.isTainted = self.taintEngine.taintAssignment(pc, src);
    //         }

    //         /* Create the semantics */
    //         let node2 = self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(1, op2.getBitvectorSize()));

    //         /* Create symbolic expression */
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, count, "LOOP counter operation");

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr1);
    //       }

    //       fn lzcnt_s(&mut self, inst: x86Instruction) {
    //         let dst     = inst.operands[0];
    //         let src     = inst.operands[1];
    //         let  bvSize1 = dst.get_bit_size();
    //         let  bvSize2 = src.get_bit_size();

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction;
    //         match src.getSize() {
    //           ByteSizes::BYTE => {
    //             node = self.ast_ctxt.ite(
    //               self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, bvSize2)),
    //               self.ast_ctxt.bv(bvSize2, bvSize1),
    //               self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 1, bvSize2 - 1, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //               self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 2, bvSize2 - 2, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //               self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 3, bvSize2 - 3, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //               self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 4, bvSize2 - 4, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //               self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 5, bvSize2 - 5, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //               self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 6, bvSize2 - 6, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //               self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 7, bvSize2 - 7, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //               self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 8, bvSize2 - 8, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //               self.ast_ctxt.bv(8, bvSize1))))))))));
    //             }
    //           ByteSizes::WORD => {
    //             node = self.ast_ctxt.ite(
    //                 self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, bvSize2)),
    //                 self.ast_ctxt.bv(bvSize2, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 1, bvSize2 - 1, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 2, bvSize2 - 2, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 3, bvSize2 - 3, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 4, bvSize2 - 4, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 5, bvSize2 - 5, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 6, bvSize2 - 6, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 7, bvSize2 - 7, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 8, bvSize2 - 8, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 9, bvSize2 - 9, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 10, bvSize2 - 10, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 11, bvSize2 - 11, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 12, bvSize2 - 12, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 13, bvSize2 - 13, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 14, bvSize2 - 14, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 15, bvSize2 - 15, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 16, bvSize2 - 16, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                 self.ast_ctxt.bv(16, bvSize1))))))))))))))))));
    //             }
    //           ByteSizes::DWORD => {
    //             node = self.ast_ctxt.ite(
    //                 self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, bvSize2)),
    //                 self.ast_ctxt.bv(bvSize2, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 1, bvSize2 - 1, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 2, bvSize2 - 2, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 3, bvSize2 - 3, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 4, bvSize2 - 4, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 5, bvSize2 - 5, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 6, bvSize2 - 6, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 7, bvSize2 - 7, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 8, bvSize2 - 8, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 9, bvSize2 - 9, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 10, bvSize2 - 10, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 11, bvSize2 - 11, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 12, bvSize2 - 12, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 13, bvSize2 - 13, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 14, bvSize2 - 14, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 15, bvSize2 - 15, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 16, bvSize2 - 16, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 17, bvSize2 - 17, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(16, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 18, bvSize2 - 18, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(17, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 19, bvSize2 - 19, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(18, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 20, bvSize2 - 20, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(19, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 21, bvSize2 - 21, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(20, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 22, bvSize2 - 22, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(21, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 23, bvSize2 - 23, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(22, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 24, bvSize2 - 24, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(23, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 25, bvSize2 - 25, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(24, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 26, bvSize2 - 26, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(25, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 27, bvSize2 - 27, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(26, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 28, bvSize2 - 28, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(27, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 29, bvSize2 - 29, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(28, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 30, bvSize2 - 30, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(29, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 31, bvSize2 - 31, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(30, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 32, bvSize2 - 32, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(31, bvSize1),
    //                 self.ast_ctxt.bv(32, bvSize1))))))))))))))))))))))))))))))))));
    //             }
    //           ByteSizes::QWORD => {
    //             node = self.ast_ctxt.ite(
    //                 self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, bvSize2)),
    //                 self.ast_ctxt.bv(bvSize2, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 1, bvSize2 - 1, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 2, bvSize2 - 2, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 3, bvSize2 - 3, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 4, bvSize2 - 4, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 5, bvSize2 - 5, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 6, bvSize2 - 6, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 7, bvSize2 - 7, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 8, bvSize2 - 8, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 9, bvSize2 - 9, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 10, bvSize2 - 10, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 11, bvSize2 - 11, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 12, bvSize2 - 12, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 13, bvSize2 - 13, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 14, bvSize2 - 14, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 15, bvSize2 - 15, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 16, bvSize2 - 16, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 17, bvSize2 - 17, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(16, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 18, bvSize2 - 18, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(17, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 19, bvSize2 - 19, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(18, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 20, bvSize2 - 20, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(19, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 21, bvSize2 - 21, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(20, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 22, bvSize2 - 22, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(21, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 23, bvSize2 - 23, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(22, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 24, bvSize2 - 24, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(23, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 25, bvSize2 - 25, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(24, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 26, bvSize2 - 26, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(25, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 27, bvSize2 - 27, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(26, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 28, bvSize2 - 28, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(27, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 29, bvSize2 - 29, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(28, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 30, bvSize2 - 30, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(29, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 31, bvSize2 - 31, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(30, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 32, bvSize2 - 32, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(31, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 33, bvSize2 - 33, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(32, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 34, bvSize2 - 34, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(33, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 35, bvSize2 - 35, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(34, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 36, bvSize2 - 36, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(35, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 37, bvSize2 - 37, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(36, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 38, bvSize2 - 38, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(37, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 39, bvSize2 - 39, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(38, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 40, bvSize2 - 40, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(39, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 41, bvSize2 - 41, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(40, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 42, bvSize2 - 42, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(41, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 43, bvSize2 - 43, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(42, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 44, bvSize2 - 44, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(43, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 45, bvSize2 - 45, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(44, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 46, bvSize2 - 46, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(45, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 47, bvSize2 - 47, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(46, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 48, bvSize2 - 48, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(47, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 49, bvSize2 - 49, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(48, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 50, bvSize2 - 50, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(49, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 51, bvSize2 - 51, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(50, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 52, bvSize2 - 52, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(51, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 53, bvSize2 - 53, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(52, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 54, bvSize2 - 54, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(53, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 55, bvSize2 - 55, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(54, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 56, bvSize2 - 56, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(55, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 57, bvSize2 - 57, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(56, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 58, bvSize2 - 58, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(57, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 59, bvSize2 - 59, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(58, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 60, bvSize2 - 60, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(59, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 61, bvSize2 - 61, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(60, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 62, bvSize2 - 62, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(61, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 63, bvSize2 - 63, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(62, bvSize1),
    //                 self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(bvSize2 - 64, bvSize2 - 64, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(63, bvSize1),
    //                 self.ast_ctxt.bv(64, bvSize1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    //             }
    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::lzcnt_s(): Invalid operand size.");"#)
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "LZCNT operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update symbolic flags */
    //         self.cfLzcnt_s(inst, expr, src, op1);
    //         self.zf_s(inst, expr, src);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::SF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::AF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn int3_s(&mut self, inst: x86Instruction) {
    //         /* Return a breakpoint fault */
    //         // self.exception = triton::arch::FAULT_BP;
    //       }

    //       fn mfence_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    fn mov_s(&mut self, inst: x86Instruction) {
        let dst = inst.operands[0];
        let src = inst.operands[1];
        let mut undef: bool = false;

        /* Create the semantics */
        let node = self.symbolicEngine.getOperandAst(inst, src);

        /*
         * Special cases:
         *
         * Triton defines segment registers as 32 or 64  bits vector to
         * avoid to simulate the GDT which allows users to directly define
         * their segments offset.
         *
         * The code below, handles the case: MOV r/m{16/32/64}, Sreg
         */
        if (src.getType() == triton::arch::OP_REG) {
            let id: u32 = src.getConstRegister().getId();
            if (id >= triton::arch::ID_REG_X86_CS && id <= triton::arch::ID_REG_X86_SS) {
                node = self.ast_ctxt.extract(dst.get_bit_size() - 1, 0, node);
            }
            if (id >= triton::arch::ID_REG_X86_CR0 && id <= triton::arch::ID_REG_X86_CR15) {
                undef = true;
            }
        }

        /*
         * The code below, handles the case: MOV Sreg, r/m{16/32/64}
         */
        if (dst.getType() == triton::arch::OP_REG) {
            let id: u32 = dst.getConstRegister().getId();
            if (id >= triton::arch::ID_REG_X86_CS && id <= triton::arch::ID_REG_X86_SS) {
                node = self.ast_ctxt.extract(BitSizes::WORD - 1, 0, node);
            }
            if (id >= triton::arch::ID_REG_X86_CR0 && id <= triton::arch::ID_REG_X86_CR15) {
                undef = true;
            }
        }

        /* Create symbolic expression */
        let expr = self
            .symbolicEngine
            .createSymbolicExpression(inst, node, dst, "MOV operation");

        /* Spread taint */
        // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

        /* Tag undefined flags */
        if (undef) {
            self.undefined_s(inst, Register::AF);
            self.undefined_s(inst, Register::CF);
            self.undefined_s(inst, Register::OF);
            self.undefined_s(inst, Register::PF);
            self.undefined_s(inst, Register::SF);
            self.undefined_s(inst, Register::ZF);
        }

        /* Update the symbolic control flow */
        self.controlFlow_s(inst);
    }

    //       fn movabs_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVABS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movapd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVAPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movaps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVAPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movbe_s(&mut self, inst: x86Instruction) {
    //         let &dst = inst.operands[0];
    //         let &src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut exprs: Vec<Instruction> = Vec::new();
    //         for i in 0..src.getSize() {
    //           exprs.push(self.ast_ctxt.extract(BitSizes::BYTE * i + (BitSizes::BYTE - 1),
    //                                                  BitSizes::BYTE * i,
    //                                                  op));
    //         }
    //         let node = self.ast_ctxt.concat(exprs);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVBE operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction ;

    //         match dst.get_bit_size() {
    //           /* GPR 32-bits */
    //           BitSizes::DWORD => {
    //             node = self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op2);
    //             }

    //           /* MMX 64-bits */
    //           BitSizes::QWORD => {
    //             node = self.ast_ctxt.zx(BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op2));
    //             }

    //           /* XMM 128-bits */
    //           BitSizes::DQWORD => {
    //             node = self.ast_ctxt.zx(BitSizes::QWORD + BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op2));
    //             }
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVD operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movddup_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.concat(self.ast_ctxt.extract(BitSizes::QWORD-1, 0, op2), self.ast_ctxt.extract(BitSizes::QWORD-1, 0, op2));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVDDUP operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movdq2q_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.extract(BitSizes::QWORD-1, 0, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVDQ2Q operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movdqa_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVDQA operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movdqu_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVDQU operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movhlps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.concat(
    //                       self.ast_ctxt.extract((BitSizes::DQWORD - 1), BitSizes::QWORD, op1), /* Destination[127..64] unchanged */
    //                       self.ast_ctxt.extract((BitSizes::DQWORD - 1), BitSizes::QWORD, op2)  /* Destination[63..0] = Source[127..64]; */
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVHLPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movhpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction ;

    //         /* xmm, m64 */
    //         if (dst.getSize() == ByteSizes::DQWORD) {
    //           node = self.ast_ctxt.concat(
    //                    self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op2), /* Destination[127..64] = Source */
    //                    self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op1)  /* Destination[63..0] unchanged */
    //                  );
    //         }

    //         /* m64, xmm */
    //         else {
    //           node = self.ast_ctxt.extract((BitSizes::DQWORD - 1), BitSizes::QWORD, op2); /* Destination[63..00] = Source[127..64] */
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVHPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movhps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction ;

    //         /* xmm, m64 */
    //         if (dst.getSize() == ByteSizes::DQWORD) {
    //           node = self.ast_ctxt.concat(
    //                    self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op2), /* Destination[127..64] = Source */
    //                    self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op1)  /* Destination[63..0] unchanged */
    //                  );
    //         }

    //         /* m64, xmm */
    //         else {
    //           node = self.ast_ctxt.extract((BitSizes::DQWORD - 1), BitSizes::QWORD, op2); /* Destination[63..00] = Source[127..64] */
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVHPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movlhps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.concat(
    //                       self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op2), /* Destination[127..64] = Source[63..0] */
    //                       self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op1)  /* Destination[63..0] unchanged */
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVLHPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movlpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction ;

    //         /* xmm, m64 */
    //         if (dst.getSize() == ByteSizes::DQWORD) {
    //           node = self.ast_ctxt.concat(
    //                    self.ast_ctxt.extract((BitSizes::DQWORD - 1), BitSizes::QWORD, op1), /* Destination[127..64] unchanged */
    //                    self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op2)                /* Destination[63..0] = Source */
    //                  );
    //         }

    //         /* m64, xmm */
    //         else {
    //           node = self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op2); /* Destination = Source[63..00] */
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVLPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movlps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction ;

    //         /* xmm, m64 */
    //         if (dst.getSize() == ByteSizes::DQWORD) {
    //           node = self.ast_ctxt.concat(
    //                    self.ast_ctxt.extract((BitSizes::DQWORD - 1), BitSizes::QWORD, op1), /* Destination[127..64] unchanged */
    //                    self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op2)                /* Destination[63..0] = Source */
    //                  );
    //         }

    //         /* m64, xmm */
    //         else {
    //           node = self.ast_ctxt.extract((BitSizes::QWORD - 1), 0, op2); /* Destination = Source[63..00] */
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVLPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movmskpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.zx(30,                       /* Destination[2..31] = 0        */
    //                       self.ast_ctxt.concat(
    //                         self.ast_ctxt.extract(127, 127, op2),  /* Destination[1] = Source[127]; */
    //                         self.ast_ctxt.extract(63, 63, op2)     /* Destination[0] = Source[63];  */
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVMSKPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movmskps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut signs: Vec<Instruction> = Vec::new();
    //         signs.reserve(4);

    //         signs.push(self.ast_ctxt.extract(127, 127, op2)); /* Destination[3] = Source[127]; */
    //         signs.push(self.ast_ctxt.extract(95, 95,   op2)); /* Destination[2] = Source[95];  */
    //         signs.push(self.ast_ctxt.extract(63, 63,   op2)); /* Destination[1] = Source[63];  */
    //         signs.push(self.ast_ctxt.extract(31, 31,   op2)); /* Destination[0] = Source[31];  */
    //         let node = self.ast_ctxt.zx(28, self.ast_ctxt.concat(signs));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVMSKPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movntdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVNTDQ operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movnti_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVNTI operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movntpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVNTPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movntps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVNTPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movntq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVNTQ operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movshdup_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut bytes: Vec<Instruction> = Vec::new();
    //         bytes.reserve(4);

    //         bytes.push(self.ast_ctxt.extract(127, 96, op2));
    //         bytes.push(self.ast_ctxt.extract(127, 96, op2));
    //         bytes.push(self.ast_ctxt.extract(63, 32, op2));
    //         bytes.push(self.ast_ctxt.extract(63, 32, op2));

    //         let node = self.ast_ctxt.concat(bytes);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVSHDUP operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movsldup_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut bytes: Vec<Instruction> = Vec::new();
    //         bytes.reserve(4);

    //         bytes.push(self.ast_ctxt.extract(95, 64, op2));
    //         bytes.push(self.ast_ctxt.extract(95, 64, op2));
    //         bytes.push(self.ast_ctxt.extract(31, 0, op2));
    //         bytes.push(self.ast_ctxt.extract(31, 0, op2));

    //         let node = self.ast_ctxt.concat(bytes);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVSLDUP operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction;

    //         /* when operating on MMX technology registers and memory locations */
    //         if (dst.get_bit_size() == BitSizes::QWORD && src.get_bit_size() == BitSizes::QWORD) {
    //           node = op2;
    //         }

    //         /* when source and destination operands are XMM registers */
    //         else if (dst.get_bit_size() == BitSizes::DQWORD && src.get_bit_size() == BitSizes::DQWORD) {
    //           node = self.ast_ctxt.concat(
    //                   self.ast_ctxt.extract(BitSizes::DQWORD-1, BitSizes::QWORD, self.symbolicEngine.getOperandAst(inst, dst)),
    //                   self.ast_ctxt.extract(BitSizes::QWORD-1, 0, op2)
    //                  );
    //         }

    //         /* when source operand is XMM register and destination operand is memory location */
    //         else if (dst.get_bit_size() < src.get_bit_size()) {
    //           node = self.ast_ctxt.extract(BitSizes::QWORD-1, 0, op2);
    //         }

    //         /* when source operand is memory location and destination operand is XMM register */
    //         else if (dst.get_bit_size() > src.get_bit_size()) {
    //           node = self.ast_ctxt.zx(BitSizes::QWORD, op2);
    //         }

    //         /* Invalid operation */
    //         else {
    //           todo!(r#"triton::exceptions::Semantics("x86Semantics::movq_s(): Invalid operation.");"#);
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVQ operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD && src.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // if (dst.get_bit_size() == BitSizes::DQWORD && src.get_bit_size() == BitSizes::DQWORD){
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // }else{
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // }
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movq2dq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.zx(BitSizes::QWORD, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVQ2DQ operation");

    //         /* TODO @fvrmatteo: the x87 FPU top-of-stack pointer is set to 0 and the x87 FPU tag word is set to all 0s [valid] */
    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movsb_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index1 = Operand::Register(Register::DI.full_register());
    //         let  index2 = Operand::Register(Register::SI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index2);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::BYTE, index1.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::BYTE, index1.get_bit_size()))
    //                      );
    //         let node3 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::BYTE, index2.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::BYTE, index2.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "MOVSB operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index1, index1);
    //         // expr3.isTainted = self.taintEngine.taintUnion(index2, index2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movsd_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index1 = Operand::Register(Register::DI.full_register());
    //         let  index2 = Operand::Register(Register::SI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /*
    //          * F2 0F 10 /r MOVSD xmm1, xmm2
    //          * F2 0F 10 /r MOVSD xmm1, m64
    //          */
    //         if (dst.get_bit_size() == BitSizes::DQWORD) {
    //           let op1  = self.symbolicEngine.getOperandAst(inst, src);
    //           let op2  = self.symbolicEngine.getOperandAst(dst);

    //           let node = self.ast_ctxt.concat(
    //                         self.ast_ctxt.extract(127, 64, op2),
    //                         self.ast_ctxt.extract(63, 0, op1)
    //                       );

    //           let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVSD operation");
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         }

    //         /*
    //          * F2 0F 11 /r MOVSD m64, xmm2
    //          */
    //         else if (dst.get_bit_size() == BitSizes::QWORD && src.get_bit_size() == BitSizes::DQWORD) {
    //           let op1  = self.symbolicEngine.getOperandAst(inst, src);
    //           let node = self.ast_ctxt.extract(63, 0, op1);
    //           let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVSD operation");
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         }

    //         /* A5 MOVSD */
    //         else {
    //           /* Create symbolic operands */
    //           let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //           let op2 = self.symbolicEngine.getOperandAst(inst, index1);
    //           let op3 = self.symbolicEngine.getOperandAst(inst, index2);
    //           let op4 = self.symbolicEngine.getOperandAst(inst, df);

    //           /* Create the semantics */
    //           let node1 = op1;
    //           let node2 = self.ast_ctxt.ite(
    //                          self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                          self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::DWORD, index1.get_bit_size())),
    //                          self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::DWORD, index1.get_bit_size()))
    //                        );
    //           let node3 = self.ast_ctxt.ite(
    //                          self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                          self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::DWORD, index2.get_bit_size())),
    //                          self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::DWORD, index2.get_bit_size()))
    //                        );

    //           /* Create symbolic expression */
    //           let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "MOVSD operation");
    //           let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
    //           let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

    //           /* Spread taint */
    //         //   expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         //   expr2.isTainted = self.taintEngine.taintUnion(index1, index1);
    //         //   expr3.isTainted = self.taintEngine.taintUnion(index2, index2);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movupd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVUPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movups_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVUPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movss_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = op;
    //         if (src.getType() == OP_REG) {
    //           node = self.ast_ctxt.extract(BitSizes::DWORD - 1, 0, node);
    //           if (dst.getType() == OP_REG) {
    //             let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //             let upper = self.ast_ctxt.extract(BitSizes::DQWORD - 1, BitSizes::DWORD, op1);
    //             node = self.ast_ctxt.concat(upper, node);
    //           }
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVSS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movsq_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index1 = Operand::Register(Register::DI.full_register());
    //         let  index2 = Operand::Register(Register::SI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index2);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::QWORD, index1.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::QWORD, index1.get_bit_size()))
    //                      );
    //         let node3 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::QWORD, index2.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::QWORD, index2.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "MOVSQ operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index1, index1);
    //         // expr3.isTainted = self.taintEngine.taintUnion(index2, index2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movsw_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index1 = Operand::Register(Register::DI.full_register());
    //         let  index2 = Operand::Register(Register::SI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index2);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::WORD, index1.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::WORD, index1.get_bit_size()))
    //                      );
    //         let node3 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::WORD, index2.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::WORD, index2.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "MOVSW operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index1, "Index (DI) operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, index2, "Index (SI) operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index1, index1);
    //         // expr3.isTainted = self.taintEngine.taintUnion(index2, index2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movsx_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.sx(dst.get_bit_size() - src.get_bit_size(), op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVSX operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movsxd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.sx(dst.get_bit_size() - src.get_bit_size(), op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVSXD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn movzx_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MOVZX operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn mul_s(&mut self, inst: x86Instruction) {
    //         let src2 = inst.operands[0];

    //         match src2.getSize() {

    //           /* AX = AL * r/m8 */
    //           ByteSizes::BYTE => {
    //             let dst  = Operand::Register(Register::AX);
    //             let src1 = Operand::Register(Register::AL);
    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //             let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //             /* Create the semantics */
    //             let node = self.ast_ctxt.bvmul(self.ast_ctxt.zx(BitSizes::BYTE, op1), self.ast_ctxt.zx(BitSizes::BYTE, op2));
    //             /* Create symbolic expression */
    //             let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "MUL operation");
    //             /* Apply the taint */
    //             // expr.isTainted = self.taintEngine.taintUnion(dst, src2);
    //             /* Update symbolic flags */
    //             let ah = self.ast_ctxt.extract((BitSizes::WORD - 1), BitSizes::BYTE, node);
    //             self.cfMul_s(inst, expr, src2, ah);
    //             self.ofMul_s(inst, expr, src2, ah);
    //           }

    //           /* DX:AX = AX * r/m16 */
    //           ByteSizes::WORD => {
    //             let dst1 = Operand::Register(Register::AX);
    //             let dst2 = Operand::Register(Register::DX);
    //             let src1 = Operand::Register(Register::AX);
    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //             let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //             /* Create symbolic expression for ax */
    //             let ax    = self.ast_ctxt.bvmul(op1, op2);
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, ax, dst1, "MUL operation");
    //             /* Apply the taint */
    //             // expr1.isTainted = self.taintEngine.taintUnion(dst1, src2);
    //             /* Create symbolic expression for dx */
    //             let node  = self.ast_ctxt.bvmul(self.ast_ctxt.zx(BitSizes::WORD, op1), self.ast_ctxt.zx(BitSizes::WORD, op2));
    //             let dx    = self.ast_ctxt.extract((BitSizes::DWORD - 1), BitSizes::WORD, node);
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, dx, dst2, "MUL operation");
    //             /* Apply the taint */
    //             // expr2.isTainted = self.taintEngine.taintUnion(dst2, src2);
    //             // expr2.isTainted = self.taintEngine.taintUnion(dst2, src1);
    //             /* Update symbolic flags */
    //             self.cfMul_s(inst, expr2, src2, dx);
    //             self.ofMul_s(inst, expr2, src2, dx);
    //           }

    //           /* EDX:EAX = EAX * r/m32 */
    //           ByteSizes::DWORD => {
    //             let dst1 = Operand::Register(Register::EAX);
    //             let dst2 = Operand::Register(Register::EDX);
    //             let src1 = Operand::Register(Register::EAX);
    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //             let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //             /* Create symbolic expression for eax */
    //             let eax   = self.ast_ctxt.bvmul(op1, op2);
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, eax, dst1, "MUL operation");
    //             /* Apply the taint */
    //             // expr1.isTainted = self.taintEngine.taintUnion(dst1, src2);
    //             /* Create symbolic expression for edx */
    //             let node  = self.ast_ctxt.bvmul(self.ast_ctxt.zx(BitSizes::DWORD, op1), self.ast_ctxt.zx(BitSizes::DWORD, op2));
    //             let edx   = self.ast_ctxt.extract((BitSizes::QWORD - 1), BitSizes::DWORD, node);
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, edx, dst2, "MUL operation");
    //             /* Apply the taint */
    //             // expr2.isTainted = self.taintEngine.taintUnion(dst2, src2);
    //             // expr2.isTainted = self.taintEngine.taintUnion(dst2, src1);
    //             /* Update symbolic flags */
    //             self.cfMul_s(inst, expr2, src2, edx);
    //             self.ofMul_s(inst, expr2, src2, edx);
    //           }

    //           /* RDX:RAX = RAX * r/m64 */
    //           ByteSizes::QWORD => {
    //             let dst1 = Operand::Register(Register::RAX);
    //             let dst2 = Operand::Register(Register::RDX);
    //             let src1 = Operand::Register(Register::RAX);
    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //             let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //             /* Create the semantics */
    //             /* Create symbolic expression for eax */
    //             let rax = self.ast_ctxt.bvmul(op1, op2);
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, rax, dst1, "MUL operation");
    //             /* Apply the taint */
    //             // expr1.isTainted = self.taintEngine.taintUnion(dst1, src2);
    //             /* Create symbolic expression for rdx */
    //             let node = self.ast_ctxt.bvmul(self.ast_ctxt.zx(BitSizes::QWORD, op1), self.ast_ctxt.zx(BitSizes::QWORD, op2));
    //             let rdx = self.ast_ctxt.extract((BitSizes::DQWORD - 1), BitSizes::QWORD, node);
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, rdx, dst2, "MUL operation");
    //             /* Apply the taint */
    //             // expr2.isTainted = self.taintEngine.taintUnion(dst2, src2);
    //             // expr2.isTainted = self.taintEngine.taintUnion(dst2, src1);
    //             /* Update symbolic flags */
    //             self.cfMul_s(inst, expr2, src2, rdx);
    //             self.ofMul_s(inst, expr2, src2, rdx);
    //           }

    //         }

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::SF);
    //         self.undefined_s(inst, Register::ZF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn mulx_s(&mut self, inst: x86Instruction) {
    //         match inst.operands[0].getSize() {

    //           /* r32a, r32b, r/m32 */
    //           ByteSizes::DWORD => {
    //             let dst1 = inst.operands[0];
    //             let dst2 = inst.operands[1];
    //             let  src1 = inst.operands[2];
    //             let  src2 = Operand::Register(Register::EDX);

    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //             let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //             /* Create the semantics */
    //             let node  = self.ast_ctxt.bvmul(self.ast_ctxt.zx(BitSizes::DWORD, op1), self.ast_ctxt.zx(BitSizes::DWORD, op2));
    //             let node1 = self.ast_ctxt.bvmul(op1, op2);
    //             let node2 = self.ast_ctxt.extract((BitSizes::QWORD - 1), BitSizes::DWORD, node);

    //             /* Create symbolic expression */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst2, "MULX operation");
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst1, "MULX operation");

    //             /* Apply the taint */
    //             // expr1.isTainted = self.taintEngine.taintUnion(dst2, src1);
    //             // expr1.isTainted = self.taintEngine.taintUnion(dst2, src2);

    //             // expr2.isTainted = self.taintEngine.taintUnion(dst1, src1);
    //             // expr2.isTainted = self.taintEngine.taintUnion(dst1, src2);
    //           }

    //           /* r64a, r64b, r/m64 */
    //           ByteSizes::QWORD => {
    //             let dst1 = inst.operands[0];
    //             let dst2 = inst.operands[1];
    //             let  src1 = inst.operands[2];
    //             let  src2 = Operand::Register(Register::RDX);

    //             /* Create symbolic operands */
    //             let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //             let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //             /* Create the semantics */
    //             let node  = self.ast_ctxt.bvmul(self.ast_ctxt.zx(BitSizes::QWORD, op1), self.ast_ctxt.zx(BitSizes::QWORD, op2));
    //             let node1 = self.ast_ctxt.bvmul(op1, op2);
    //             let node2 = self.ast_ctxt.extract((BitSizes::DQWORD - 1), BitSizes::QWORD, node);

    //             /* Create symbolic expression for eax */
    //             let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst2, "MULX operation");
    //             let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst1, "MULX operation");

    //             /* Apply the taint */
    //             // expr1.isTainted = self.taintEngine.taintUnion(dst2, src1);
    //             // expr1.isTainted = self.taintEngine.taintUnion(dst2, src2);

    //             // expr2.isTainted = self.taintEngine.taintUnion(dst1, src1);
    //             // expr2.isTainted = self.taintEngine.taintUnion(dst1, src2);
    //           }

    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn neg_s(&mut self, inst: x86Instruction) {
    //         let src = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvneg(op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, src, "NEG operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(src, src);

    //         /* Update symbolic flags */
    //         self.afNeg_s(inst, expr, src, op1);
    //         self.cfNeg_s(inst, expr, src, op1);
    //         self.ofNeg_s(inst, expr, src, op1);
    //         self.pf_s(inst, expr, src);
    //         self.sf_s(inst, expr, src);
    //         self.zf_s(inst, expr, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn nop_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn not_s(&mut self, inst: x86Instruction) {
    //         let src = inst.operands[0];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvnot(op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, src, "NOT operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(src, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn or_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "OR operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update symbolic flags */
    //         self.clearFlag_s(inst, Register::CF, "Clears carry flag");
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.pf_s(inst, expr, dst);
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::AF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn orpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ORPD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn orps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ORPS operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn packuswb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         std::vector<triton::ast::SharedAbstractNode> ops{op2, op1};
    //         for i in 0..(ops.size()) {
    //           for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //             let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //             let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //             let signed_word = self.ast_ctxt.extract(high, low, ops[i]);
    //             pck.push(self.ast_ctxt.ite(
    //                            self.ast_ctxt.bvsge(signed_word, self.ast_ctxt.bv(0xff, BitSizes::WORD)),
    //                            self.ast_ctxt.bv(0xff, BitSizes::BYTE),
    //                            self.ast_ctxt.ite(
    //                              self.ast_ctxt.bvsle(signed_word, self.ast_ctxt.bv(0x00, BitSizes::WORD)),
    //                              self.ast_ctxt.bv(0x00, BitSizes::BYTE),
    //                              self.ast_ctxt.extract(BitSizes::BYTE - 1, 0, signed_word)))
    //                          );
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PACKUSWB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn packssdw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         std::vector<triton::ast::SharedAbstractNode> ops{op2, op1};

    //           for idx in 0..(ops.size()) {
    //             for i in 0..(dst.getSize() / ByteSizes::DWORD) {
    //               let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::DWORD);
    //               let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (i * BitSizes::DWORD);
    //               let signed_dword = self.ast_ctxt.extract(high, low, ops[idx]);
    //               pck.push(self.ast_ctxt.ite(
    //                       self.ast_ctxt.bvsge(signed_dword, self.ast_ctxt.bv(0x7fff, BitSizes::DWORD)),
    //                       self.ast_ctxt.bv(0x7fff, BitSizes::WORD),
    //                       self.ast_ctxt.ite(
    //                               self.ast_ctxt.bvsle(signed_dword, self.ast_ctxt.bv(0xffff8000, BitSizes::DWORD)),
    //                               self.ast_ctxt.bv(0x8000, BitSizes::WORD),
    //                               self.ast_ctxt.extract(BitSizes::WORD - 1, 0, signed_dword)))
    //               );
    //             }
    //           }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PACKSSDW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn packsswb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         std::vector<triton::ast::SharedAbstractNode> ops{op2, op1};
    //         for i in 0..(ops.size()) {
    //           for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //             let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //             let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //             let signed_word = self.ast_ctxt.extract(high, low, ops[i]);
    //             pck.push(self.ast_ctxt.ite(
    //                            self.ast_ctxt.bvsge(signed_word, self.ast_ctxt.bv(0x007f, BitSizes::WORD)),
    //                            self.ast_ctxt.bv(0x7f, BitSizes::BYTE),
    //                            self.ast_ctxt.ite(
    //                              self.ast_ctxt.bvsle(signed_word, self.ast_ctxt.bv(0xff80, BitSizes::WORD)),
    //                              self.ast_ctxt.bv(0x80, BitSizes::BYTE),
    //                              self.ast_ctxt.extract(BitSizes::BYTE - 1, 0, signed_word)))
    //                          );
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PACKSSWB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn paddb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(16);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(127, 120, op1), self.ast_ctxt.extract(127, 120, op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(119, 112, op1), self.ast_ctxt.extract(119, 112, op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(111, 104, op1), self.ast_ctxt.extract(111, 104, op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(103, 96,  op1), self.ast_ctxt.extract(103, 96,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(95,  88,  op1), self.ast_ctxt.extract(95,  88,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(87,  80,  op1), self.ast_ctxt.extract(87,  80,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(79,  72,  op1), self.ast_ctxt.extract(79,  72,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(71,  64,  op1), self.ast_ctxt.extract(71,  64,  op2)));

    //             // todo: duplicated below
    //                         packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(63,  56,  op1), self.ast_ctxt.extract(63,  56,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(55,  48,  op1), self.ast_ctxt.extract(55,  48,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(47,  40,  op1), self.ast_ctxt.extract(47,  40,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(39,  32,  op1), self.ast_ctxt.extract(39,  32,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(31,  24,  op1), self.ast_ctxt.extract(31,  24,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(23,  16,  op1), self.ast_ctxt.extract(23,  16,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(15,  8,   op1), self.ast_ctxt.extract(15,  8,   op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(7,   0,   op1), self.ast_ctxt.extract(7,   0,   op2)));
    // }

    //           /* MMX */
    //           BitSizes::QWORD =>{
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(63,  56,  op1), self.ast_ctxt.extract(63,  56,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(55,  48,  op1), self.ast_ctxt.extract(55,  48,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(47,  40,  op1), self.ast_ctxt.extract(47,  40,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(39,  32,  op1), self.ast_ctxt.extract(39,  32,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(31,  24,  op1), self.ast_ctxt.extract(31,  24,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(23,  16,  op1), self.ast_ctxt.extract(23,  16,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(15,  8,   op1), self.ast_ctxt.extract(15,  8,   op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(7,   0,   op1), self.ast_ctxt.extract(7,   0,   op2)));
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::paddb_s(): Invalid operand size.");"#)

    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PADDB operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn paddd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(4);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(127, 96, op1), self.ast_ctxt.extract(127, 96, op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(95,  64, op1), self.ast_ctxt.extract(95,  64, op2)));

    //             // todo: duplicated below
    //                         packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(63,  32, op1), self.ast_ctxt.extract(63,  32, op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(31,  0,  op1), self.ast_ctxt.extract(31,  0,  op2)));
    //         }

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(63,  32, op1), self.ast_ctxt.extract(63,  32, op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(31,  0,  op1), self.ast_ctxt.extract(31,  0,  op2)));
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::paddd_s(): Invalid operand size.");"#)

    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PADDD operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn paddq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(2);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(127, 64, op1), self.ast_ctxt.extract(127, 64, op2)));

    //             // todo: duplicated below
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(63,  0,  op1), self.ast_ctxt.extract(63,  0,  op2)));
    // }
    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(63,  0,  op1), self.ast_ctxt.extract(63,  0,  op2)));
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::paddq_s(): Invalid operand size.");"#)

    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PADDQ operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn paddw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(8);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(127, 112, op1), self.ast_ctxt.extract(127, 112, op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(111, 96,  op1), self.ast_ctxt.extract(111, 96,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(95,  80,  op1), self.ast_ctxt.extract(95,  80,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(79,  64,  op1), self.ast_ctxt.extract(79,  64,  op2)));

    //             // todo: duplicated below
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(63,  48,  op1), self.ast_ctxt.extract(63,  48,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(47,  32,  op1), self.ast_ctxt.extract(47,  32,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(31,  16,  op1), self.ast_ctxt.extract(31,  16,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(15,  0,   op1), self.ast_ctxt.extract(15,  0,   op2)));
    //           }

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(63,  48,  op1), self.ast_ctxt.extract(63,  48,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(47,  32,  op1), self.ast_ctxt.extract(47,  32,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(31,  16,  op1), self.ast_ctxt.extract(31,  16,  op2)));
    //             packed.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(15,  0,   op1), self.ast_ctxt.extract(15,  0,   op2)));
    //           }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::paddw_s(): Invalid operand size.");"#)

    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PADDW operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn palignr_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let size = 2 * dst.get_bit_size();
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.ast_ctxt.zx(size - src2.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src2));

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.extract(
    //                       dst.get_bit_size() - 1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         self.ast_ctxt.concat(op1, op2),
    //                         self.ast_ctxt.bvmul(
    //                           self.ast_ctxt.ite(
    //                             self.ast_ctxt.bvuge(op3, self.ast_ctxt.bv(2 * dst.getSize(), size)),
    //                             self.ast_ctxt.bv(2 * dst.getSize(), size),
    //                             op3),
    //                           self.ast_ctxt.bv(BitSizes::BYTE, size)
    //                         )));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PALIGNR operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pand_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PAND operation");

    //         /* Update the x87 FPU Tag Word */
    //         self.updateFTW(inst, expr);

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pandn_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(self.ast_ctxt.bvnot(op1), op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PANDN operation");

    //         /* Update the x87 FPU Tag Word */
    //         self.updateFTW(inst, expr);

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pause_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pavgb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(
    //             self.ast_ctxt.extract(BitSizes::BYTE-1, 0,
    //               self.ast_ctxt.bvlshr(
    //                 self.ast_ctxt.bvadd(
    //                   self.ast_ctxt.bvadd(
    //                     self.ast_ctxt.zx(1, self.ast_ctxt.extract(high, low, op1)),
    //                     self.ast_ctxt.zx(1, self.ast_ctxt.extract(high, low, op2))
    //                   ),
    //                   self.ast_ctxt.bv(1, BitSizes::BYTE+1)
    //                 ),
    //                 self.ast_ctxt.bv(1, BitSizes::BYTE+1)
    //               )
    //             )
    //           );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PAVGB operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pavgw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(
    //             self.ast_ctxt.extract(BitSizes::WORD-1, 0,
    //               self.ast_ctxt.bvlshr(
    //                 self.ast_ctxt.bvadd(
    //                   self.ast_ctxt.bvadd(
    //                     self.ast_ctxt.zx(1, self.ast_ctxt.extract(high, low, op1)),
    //                     self.ast_ctxt.zx(1, self.ast_ctxt.extract(high, low, op2))
    //                   ),
    //                   self.ast_ctxt.bv(1, BitSizes::WORD+1)
    //                 ),
    //                 self.ast_ctxt.bv(1, BitSizes::WORD+1)
    //               )
    //             )
    //           );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PAVGW operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pcmpeqb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.equal(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xff, BitSizes::BYTE),
    //                           self.ast_ctxt.bv(0x00, BitSizes::BYTE))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PCMPEQB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pcmpeqd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.equal(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffffffff, BitSizes::DWORD),
    //                           self.ast_ctxt.bv(0x00000000, BitSizes::DWORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PCMPEQD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pcmpeqw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.equal(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffff, BitSizes::WORD),
    //                           self.ast_ctxt.bv(0x0000, BitSizes::WORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PCMPEQW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pcmpgtb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsgt(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xff, BitSizes::BYTE),
    //                           self.ast_ctxt.bv(0x00, BitSizes::BYTE))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PCMPGTB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pcmpgtd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsgt(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffffffff, BitSizes::DWORD),
    //                           self.ast_ctxt.bv(0x00000000, BitSizes::DWORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PCMPGTD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pcmpgtw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsgt(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffff, BitSizes::WORD),
    //                           self.ast_ctxt.bv(0x0000, BitSizes::WORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PCMPGTW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmaxsb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsle(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMAXSB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pextrb_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         let node = self.ast_ctxt.extract(BitSizes::BYTE - 1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bv(((op3.evaluate() & 0x0f) * BitSizes::BYTE), op2.getBitvectorSize())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PEXTRB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pextrd_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         let node = self.ast_ctxt.extract(BitSizes::DWORD - 1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bv(((op3.evaluate() & 0x3) * BitSizes::DWORD), op2.getBitvectorSize())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PEXTRD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pextrq_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         let node = self.ast_ctxt.extract(BitSizes::QWORD - 1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bv(((op3.evaluate() & 0x1) * BitSizes::QWORD), op2.getBitvectorSize())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PEXTRQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pextrw_s(&mut self, inst: x86Instruction) {
    //         let mut count: u32 = 0;
    //         let dst            = inst.operands[0];
    //         let src1           = inst.operands[1];
    //         let src2           = inst.operands[2];

    //         /*
    //          * When specifying a word location in an MMX technology register, the
    //          * 2 least-significant bits of the count operand specify the location;
    //          * for an XMM register, the 3 least-significant bits specify the
    //          * location.
    //          */
    //         if (src1.get_bit_size() == BitSizes::QWORD) {
    //           count = 0x03;
    //         }
    //         else {
    //           count = 0x07;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         let node = self.ast_ctxt.extract(BitSizes::WORD - 1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bv(((op3.evaluate() & count) * BitSizes::WORD), op2.getBitvectorSize())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PEXTRW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pinsrb_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         // SEL  = COUNT[3:0];
    //         // MASK = (0FFH << (SEL * 8));
    //         let sel: u64 = op3.evaluate() as u64 & 0x0f;
    //         let mask: u128 = 0xff;
    //         mask = mask << (sel * 8);

    //         // TEMP = ((SRC[7:0] << (SEL * 8)) AND MASK);
    //         let temp = self.ast_ctxt.bvand(
    //                       self.ast_ctxt.bvshl(
    //                         self.ast_ctxt.zx(120, self.ast_ctxt.extract(7, 0, op2)),
    //                         self.ast_ctxt.bv(sel * 8, 128)
    //                       ),
    //                       self.ast_ctxt.bv(mask, 128)
    //                     );

    //         // DEST = ((DEST AND NOT MASK) OR TEMP);
    //         let node = self.ast_ctxt.bvor(
    //                       self.ast_ctxt.bvand(
    //                         op1,
    //                         self.ast_ctxt.bvnot(self.ast_ctxt.bv(mask, 128))
    //                       ),
    //                       temp
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PINSRB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pinsrd_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         // SEL  = COUNT[1:0];
    //         // MASK = (0FFFFFFFFH << (SEL * 32));
    //         let sel: u64 = op3.evaluate() as u64 & 0x03;
    //         let mask: u128 = 0xffffffff;
    //         mask = mask << (sel * 32);

    //         // TEMP = ((SRC[31:0] << (SEL * 32)) AND MASK);
    //         let temp = self.ast_ctxt.bvand(
    //                       self.ast_ctxt.bvshl(
    //                         self.ast_ctxt.zx(96, self.ast_ctxt.extract(31, 0, op2)),
    //                         self.ast_ctxt.bv(sel * 32, 128)
    //                       ),
    //                       self.ast_ctxt.bv(mask, 128)
    //                     );

    //         // DEST = ((DEST AND NOT MASK) OR TEMP);
    //         let node = self.ast_ctxt.bvor(
    //                       self.ast_ctxt.bvand(
    //                         op1,
    //                         self.ast_ctxt.bvnot(self.ast_ctxt.bv(mask, 128))
    //                       ),
    //                       temp
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PINSRD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pinsrq_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         // SEL  = COUNT[0:0];
    //         // MASK = (0FFFFFFFFFFFFFFFFH << (SEL * 64));
    //         let sel: u64 = op3.evaluate() as u64 & 0x1;
    //         let mask: u128 = 0xffffffffffffffff;
    //         mask = mask << (sel * 64);

    //         // TEMP = ((SRC[63:0] << (SEL * 64)) AND MASK);
    //         let temp = self.ast_ctxt.bvand(
    //                       self.ast_ctxt.bvshl(
    //                         self.ast_ctxt.zx(64, self.ast_ctxt.extract(63, 0, op2)),
    //                         self.ast_ctxt.bv(sel * 64, 128)
    //                       ),
    //                       self.ast_ctxt.bv(mask, 128)
    //                     );

    //         // DEST = ((DEST AND NOT MASK) OR TEMP);
    //         let node = self.ast_ctxt.bvor(
    //                       self.ast_ctxt.bvand(
    //                         op1,
    //                         self.ast_ctxt.bvnot(self.ast_ctxt.bv(mask, 128))
    //                       ),
    //                       temp
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PINSRQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pinsrw_s(&mut self, inst: x86Instruction) {
    //         let mask: u128 = 0xffff;
    //         let sel: u64 = 0;
    //         let dst            = inst.operands[0];
    //         let src1           = inst.operands[1];
    //         let src2           = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /*
    //          * PINSRW (with 64-bit source operand)
    //          *
    //          * SEL = COUNT AND 3H;
    //          * CASE (Determine word position) {
    //          *   if SEL == 0: MASK = 000000000000FFFFH;
    //          *   if SEL == 1: MASK = 00000000FFFF0000H;
    //          *   if SEL == 2: MASK = 0000FFFF00000000H;
    //          *   if SEL == 3: MASK = FFFF000000000000H;
    //          * }
    //          */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           sel = op3.evaluate() as u64 & 0x3;
    //           match sel {
    //             1 => mask = mask << 16,
    //             2 => mask = mask << 32,
    //             3 => mask = mask << 48,
    //             _ => {},
    //           }
    //         }

    //         /*
    //          * PINSRW (with 128-bit source operand)
    //          *
    //          * SEL ← COUNT AND 7H;
    //          * CASE (Determine word position) {
    //          *   SEL == 0: MASK = 0000000000000000000000000000FFFFH;
    //          *   SEL == 1: MASK = 000000000000000000000000FFFF0000H;
    //          *   SEL == 2: MASK = 00000000000000000000FFFF00000000H;
    //          *   SEL == 3: MASK = 0000000000000000FFFF000000000000H;
    //          *   SEL == 4: MASK = 000000000000FFFF0000000000000000H;
    //          *   SEL == 5: MASK = 00000000FFFF00000000000000000000H;
    //          *   SEL == 6: MASK = 0000FFFF000000000000000000000000H;
    //          *   SEL == 7: MASK = FFFF0000000000000000000000000000H;
    //          * }
    //          */
    //         else {
    //           sel = op3.evaluate() as u64 & 0x7;
    //           match sel {
    //             1 => mask = mask << 16,
    //             2 => mask = mask << 32,
    //             3 => mask = mask << 48,
    //             4 => mask = mask << 64,
    //             5 => mask = mask << 80,
    //             6 => mask = mask << 96,
    //             7 => mask = mask << 112,
    //             _ => {}
    //           }
    //         }

    //         // TEMP = ((SRC << (SEL ∗ 16)) AND MASK);
    //         let temp = self.ast_ctxt.bvand(
    //                       self.ast_ctxt.bvshl(
    //                         self.ast_ctxt.zx(112, self.ast_ctxt.extract(15, 0, op2)),
    //                         self.ast_ctxt.bv(sel * 16, 128)
    //                       ),
    //                       self.ast_ctxt.bv(mask, 128)
    //                     );

    //         // DEST = ((DEST AND NOT MASK) OR TEMP);
    //         let node = self.ast_ctxt.bvor(
    //                       self.ast_ctxt.bvand(
    //                         op1,
    //                         self.ast_ctxt.bvnot(self.ast_ctxt.bv(mask, 128))
    //                       ),
    //                       temp
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PINSRW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmaddwd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         for i in 0..(dst.getSize() / ByteSizes::WORD).step_by(2) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           let node1 = self.ast_ctxt.bvmul(
    //                          self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op1)),
    //                          self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op2))
    //                        );
    //           high -= BitSizes::WORD;
    //           low  -= BitSizes::WORD;
    //           let node2 = self.ast_ctxt.bvmul(
    //                          self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op1)),
    //                          self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op2))
    //                        );
    //           pck.push(self.ast_ctxt.bvadd(node1, node2));
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMADDWD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmaxsd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsle(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMAXSD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmaxsw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsle(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMAXSW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmaxub_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvule(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMAXUB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmaxud_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvule(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMAXUD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmaxuw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvule(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMAXUW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pminsb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsge(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMINSB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pminsd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsge(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMINSD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pminsw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsge(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMINSW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pminub_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvuge(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMINUB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pminud_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvuge(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMINUD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pminuw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvuge(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMINUW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovmskb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut mskb: Vec<Instruction> = Vec::new();
    //         mskb.reserve(16);

    //         match src.getSize() {
    //           ByteSizes::DQWORD => {
    //             mskb.push(self.ast_ctxt.extract(127, 127, op2));
    //             mskb.push(self.ast_ctxt.extract(119, 119, op2));
    //             mskb.push(self.ast_ctxt.extract(111, 111, op2));
    //             mskb.push(self.ast_ctxt.extract(103, 103, op2));
    //             mskb.push(self.ast_ctxt.extract(95,  95,  op2));
    //             mskb.push(self.ast_ctxt.extract(87,  87,  op2));
    //             mskb.push(self.ast_ctxt.extract(79,  79,  op2));
    //             mskb.push(self.ast_ctxt.extract(71,  71,  op2));

    //             // todo: duplicated below
    //             mskb.push(self.ast_ctxt.extract(63,  63,  op2));
    //             mskb.push(self.ast_ctxt.extract(55,  55,  op2));
    //             mskb.push(self.ast_ctxt.extract(47,  47,  op2));
    //             mskb.push(self.ast_ctxt.extract(39,  39,  op2));
    //             mskb.push(self.ast_ctxt.extract(31,  31,  op2));
    //             mskb.push(self.ast_ctxt.extract(23,  23,  op2));
    //             mskb.push(self.ast_ctxt.extract(15,  15,  op2));
    //             mskb.push(self.ast_ctxt.extract(7,   7,   op2));
    //         }
    //           ByteSizes::QWORD => {
    //             mskb.push(self.ast_ctxt.extract(63,  63,  op2));
    //             mskb.push(self.ast_ctxt.extract(55,  55,  op2));
    //             mskb.push(self.ast_ctxt.extract(47,  47,  op2));
    //             mskb.push(self.ast_ctxt.extract(39,  39,  op2));
    //             mskb.push(self.ast_ctxt.extract(31,  31,  op2));
    //             mskb.push(self.ast_ctxt.extract(23,  23,  op2));
    //             mskb.push(self.ast_ctxt.extract(15,  15,  op2));
    //             mskb.push(self.ast_ctxt.extract(7,   7,   op2));
    //         }
    //         }

    //         let node = self.ast_ctxt.zx(
    //                       dst.get_bit_size() - mskb.size() as u32,
    //                       self.ast_ctxt.concat(mskb)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVMSKB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovsxbd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(4);

    //         pck.push(self.ast_ctxt.sx(BitSizes::DWORD - BitSizes::BYTE, self.ast_ctxt.extract(31, 24, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::DWORD - BitSizes::BYTE, self.ast_ctxt.extract(23, 16, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::DWORD - BitSizes::BYTE, self.ast_ctxt.extract(15, 8,  op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::DWORD - BitSizes::BYTE, self.ast_ctxt.extract(7,  0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVSXBD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovsxbq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(2);

    //         pck.push(self.ast_ctxt.sx(BitSizes::QWORD - BitSizes::BYTE, self.ast_ctxt.extract(15, 8,  op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::QWORD - BitSizes::BYTE, self.ast_ctxt.extract(7,  0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVSXBQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovsxbw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(8);

    //         pck.push(self.ast_ctxt.sx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(63, 56, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(55, 48, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(47, 40, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(39, 32, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(31, 24, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(23, 16, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(15, 8,  op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(7,  0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVSXBW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovsxdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(2);

    //         pck.push(self.ast_ctxt.sx(BitSizes::QWORD - BitSizes::DWORD, self.ast_ctxt.extract(63, 32, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::QWORD - BitSizes::DWORD, self.ast_ctxt.extract(31, 0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVSXDQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovsxwd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(4);

    //         pck.push(self.ast_ctxt.sx(BitSizes::DWORD - BitSizes::WORD, self.ast_ctxt.extract(63, 48, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::DWORD - BitSizes::WORD, self.ast_ctxt.extract(47, 32, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::DWORD - BitSizes::WORD, self.ast_ctxt.extract(31, 16, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::DWORD - BitSizes::WORD, self.ast_ctxt.extract(15, 0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVSXWD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovsxwq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(2);

    //         pck.push(self.ast_ctxt.sx(BitSizes::QWORD - BitSizes::WORD, self.ast_ctxt.extract(31, 16, op2)));
    //         pck.push(self.ast_ctxt.sx(BitSizes::QWORD - BitSizes::WORD, self.ast_ctxt.extract(15, 0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVSXWQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovzxbd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(4);

    //         pck.push(self.ast_ctxt.zx(BitSizes::DWORD - BitSizes::BYTE, self.ast_ctxt.extract(31, 24, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::DWORD - BitSizes::BYTE, self.ast_ctxt.extract(23, 16, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::DWORD - BitSizes::BYTE, self.ast_ctxt.extract(15, 8,  op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::DWORD - BitSizes::BYTE, self.ast_ctxt.extract(7,  0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVZXBD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovzxbq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(2);

    //         pck.push(self.ast_ctxt.zx(BitSizes::QWORD - BitSizes::BYTE, self.ast_ctxt.extract(15, 8,  op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::QWORD - BitSizes::BYTE, self.ast_ctxt.extract(7,  0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVZXBQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovzxbw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(8);

    //         pck.push(self.ast_ctxt.zx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(63, 56, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(55, 48, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(47, 40, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(39, 32, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(31, 24, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(23, 16, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(15, 8,  op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::WORD - BitSizes::BYTE, self.ast_ctxt.extract(7,  0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVZXBW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovzxdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(2);

    //         pck.push(self.ast_ctxt.zx(BitSizes::QWORD - BitSizes::DWORD, self.ast_ctxt.extract(63, 32, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::QWORD - BitSizes::DWORD, self.ast_ctxt.extract(31, 0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVZXDQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovzxwd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(4);

    //         pck.push(self.ast_ctxt.zx(BitSizes::DWORD - BitSizes::WORD, self.ast_ctxt.extract(63, 48, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::DWORD - BitSizes::WORD, self.ast_ctxt.extract(47, 32, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::DWORD - BitSizes::WORD, self.ast_ctxt.extract(31, 16, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::DWORD - BitSizes::WORD, self.ast_ctxt.extract(15, 0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVZXWD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmovzxwq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(2);

    //         pck.push(self.ast_ctxt.zx(BitSizes::QWORD - BitSizes::WORD, self.ast_ctxt.extract(31, 16, op2)));
    //         pck.push(self.ast_ctxt.zx(BitSizes::QWORD - BitSizes::WORD, self.ast_ctxt.extract(15, 0,  op2)));

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMOVZXWQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmulhw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           let n1 = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op1));
    //           let n2 = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op2));
    //           let node = self.ast_ctxt.extract(BitSizes::DWORD - 1, BitSizes::WORD, self.ast_ctxt.bvmul(n1, n2));
    //           pck.push(node);
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMULHW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmulld_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         for i in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (i * BitSizes::DWORD);
    //           let n1 = self.ast_ctxt.sx(BitSizes::DWORD, self.ast_ctxt.extract(high, low, op1));
    //           let n2 = self.ast_ctxt.sx(BitSizes::DWORD, self.ast_ctxt.extract(high, low, op2));
    //           let node = self.ast_ctxt.extract(BitSizes::DWORD - 1, 0, self.ast_ctxt.bvmul(n1, n2));
    //           pck.push(node);
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMULLD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmullw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           let n1 = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op1));
    //           let n2 = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op2));
    //           let node = self.ast_ctxt.extract(BitSizes::WORD - 1, 0, self.ast_ctxt.bvmul(n1, n2));
    //           pck.push(node);
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMULLW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pmuludq_s(&mut self, inst: x86Instruction) {
    //         let mut node: Instruction;
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         match dst.get_bit_size() {
    //           BitSizes::QWORD => {
    //             let n1 = self.ast_ctxt.zx(BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op1));
    //             let n2 = self.ast_ctxt.zx(BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op2));
    //             node = self.ast_ctxt.bvmul(n1, n2);
    //           }

    //           BitSizes::DQWORD => {
    //             let mut pck: Vec<Instruction> = Vec::new();
    //             pck.reserve(2);

    //             let n1 = self.ast_ctxt.zx(BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op1));
    //             let n2 = self.ast_ctxt.zx(BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op2));

    //             let n3 = self.ast_ctxt.zx(BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::QWORD+BitSizes::DWORD-1, BitSizes::QWORD, op1));
    //             let n4 = self.ast_ctxt.zx(BitSizes::DWORD, self.ast_ctxt.extract(BitSizes::QWORD+BitSizes::DWORD-1, BitSizes::QWORD, op2));

    //             pck.push(self.ast_ctxt.bvmul(n3, n4));
    //             pck.push(self.ast_ctxt.bvmul(n1, n2));

    //             node = self.ast_ctxt.concat(pck);
    //           }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::pmuludq_s(): Invalid operand size.");"#),
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PMULUDQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //         return;
    //       }

    //       fn popcnt_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bv(0, dst.get_bit_size());
    //         for i in 0..(src.get_bit_size()) {
    //           node = self.ast_ctxt.bvadd(
    //                    node,
    //                    self.ast_ctxt.zx(dst.get_bit_size() - 1, self.ast_ctxt.extract(i, i, op2))
    //                  );
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "POPCNT operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pop_s(&mut self, inst: x86Instruction) {
    //         let mut stackRelative: bool = false;
    //         let  stack         = self.architecture.get_stack_pointer();
    //         let  stackValue    = self.architecture.getConcreteRegisterValue(stack) as u64;
    //         let dst           = inst.operands[0];
    //         let  src           = Operand::Memory(MemoryAccess::new(stackValue, dst.getSize()));

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = op1;

    //         /*
    //          * Create the semantics - side effect
    //          *
    //          * Intel: If the ESP register is used as a base register for addressing a destination operand in
    //          * memory, the POP instruction computes the effective address of the operand after it increments
    //          * the ESP register.
    //          */
    //         if (dst.getType() == triton::arch::OP_MEM) {
    //           let base: Register = dst.getMemory().getConstBaseRegister();
    //           /* Check if the base register is the stack pointer */
    //           if (self.architecture.is_register_valid(base) && self.architecture.getParentRegister(base) == stack) {
    //             /* Align the stack */
    //             alignAddStack_s(inst, src.getSize());
    //             /* Re-initialize the memory access */
    //             self.symbolicEngine.initLeaAst(dst.getMemory());
    //             stackRelative = true;
    //           }
    //         }

    //         /*
    //          * Create the semantics - side effect
    //          *
    //          * Don't increment SP if the destination register is SP.
    //          */
    //         else if (dst.getType() == triton::arch::OP_REG) {
    //           if (self.architecture.getParentRegister(dst.getRegister()) == stack) {
    //             stackRelative = true;
    //           }
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "POP operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Create the semantics - side effect */
    //         if (!stackRelative){
    //           alignAddStack_s(inst, src.getSize());
    // }
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn popal_s(&mut self, inst: x86Instruction) {
    //         let stack      = self.architecture.get_stack_pointer();
    //         let stackValue = self.architecture.getConcreteRegisterValue(stack) as u64;
    //         let dst1       = Operand::Register(Register::EDI);
    //         let dst2       = Operand::Register(Register::ESI);
    //         let dst3       = Operand::Register(Register::EBP);
    //         let dst4       = Operand::Register(Register::EBX);
    //         let dst5       = Operand::Register(Register::EDX);
    //         let dst6       = Operand::Register(Register::ECX);
    //         let dst7       = Operand::Register(Register::EAX);
    //         let src1       = Operand::Memory(MemoryAccess::new(stackValue+(stack.getSize() * 0), stack.getSize()));
    //         let src2       = Operand::Memory(MemoryAccess::new(stackValue+(stack.getSize() * 1), stack.getSize()));
    //         let src3       = Operand::Memory(MemoryAccess::new(stackValue+(stack.getSize() * 2), stack.getSize()));
    //         /* stack.getSize() * 3 (ESP) is voluntarily omitted */
    //         let src4       = Operand::Memory(MemoryAccess::new(stackValue+(stack.getSize() * 4), stack.getSize()));
    //         let src5       = Operand::Memory(MemoryAccess::new(stackValue+(stack.getSize() * 5), stack.getSize()));
    //         let src6       = Operand::Memory(MemoryAccess::new(stackValue+(stack.getSize() * 6), stack.getSize()));
    //         let src7       = Operand::Memory(MemoryAccess::new(stackValue+(stack.getSize() * 7), stack.getSize()));

    //         /* Create symbolic operands and semantics */
    //         let node1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let node2 = self.symbolicEngine.getOperandAst(inst, src2);
    //         let node3 = self.symbolicEngine.getOperandAst(inst, src3);
    //         let node4 = self.symbolicEngine.getOperandAst(inst, src4);
    //         let node5 = self.symbolicEngine.getOperandAst(inst, src5);
    //         let node6 = self.symbolicEngine.getOperandAst(inst, src6);
    //         let node7 = self.symbolicEngine.getOperandAst(inst, src7);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst1, "POPAL EDI operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2, "POPAL ESI operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, dst3, "POPAL EBP operation");
    //         let expr4 = self.symbolicEngine.createSymbolicExpression(inst, node4, dst4, "POPAL EBX operation");
    //         let expr5 = self.symbolicEngine.createSymbolicExpression(inst, node5, dst5, "POPAL EDX operation");
    //         let expr6 = self.symbolicEngine.createSymbolicExpression(inst, node6, dst6, "POPAL ECX operation");
    //         let expr7 = self.symbolicEngine.createSymbolicExpression(inst, node7, dst7, "POPAL EAX operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst1, src1);
    //         // expr2.isTainted = self.taintEngine.taintAssignment(dst2, src2);
    //         // expr3.isTainted = self.taintEngine.taintAssignment(dst3, src3);
    //         // expr4.isTainted = self.taintEngine.taintAssignment(dst4, src4);
    //         // expr5.isTainted = self.taintEngine.taintAssignment(dst5, src5);
    //         // expr6.isTainted = self.taintEngine.taintAssignment(dst6, src6);
    //         // expr7.isTainted = self.taintEngine.taintAssignment(dst7, src7);

    //         /* Create the semantics - side effect */
    //         alignAddStack_s(inst, stack.getSize() * 8);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn popf_s(&mut self, inst: x86Instruction) {
    //         let  stack      = self.architecture.get_stack_pointer();
    //         let  stackValue = self.architecture.getConcreteRegisterValue(stack) as u64;
    //         let  dst1       = Operand::Register(Register::CF);
    //         let  dst2       = Operand::Register(Register::PF);
    //         let  dst3       = Operand::Register(Register::AF);
    //         let  dst4       = Operand::Register(Register::ZF);
    //         let  dst5       = Operand::Register(Register::SF);
    //         let  dst6       = Operand::Register(Register::TF);
    //         let  dst7       = Operand::Register(Register::IF);
    //         let  dst8       = Operand::Register(Register::DF);
    //         let  dst9       = Operand::Register(Register::OF);
    //         let  dst10      = Operand::Register(Register::NT);
    //         let  src        = Operand::Memory(MemoryAccess::new(stackValue, stack.getSize()));

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node1  = self.ast_ctxt.extract(0,  0,  op1);
    //         let node2  = self.ast_ctxt.extract(2,  2,  op1);
    //         let node3  = self.ast_ctxt.extract(4,  4,  op1);
    //         let node4  = self.ast_ctxt.extract(6,  6,  op1);
    //         let node5  = self.ast_ctxt.extract(7,  7,  op1);
    //         let node6  = self.ast_ctxt.extract(8,  8,  op1);
    //         let node7  = self.ast_ctxt.bvtrue(); /* IF true? */
    //         let node8  = self.ast_ctxt.extract(10, 10, op1);
    //         let node9  = self.ast_ctxt.extract(11, 11, op1);
    //         /* IOPL don't support */
    //         let node10 = self.ast_ctxt.extract(14, 14, op1);

    //         /* Create symbolic expression */
    //         let expr1  = self.symbolicEngine.createSymbolicExpression(inst, node1, dst1.getRegister(),   "POPF CF operation");
    //         let expr2  = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2.getRegister(),   "POPF PF operation");
    //         let expr3  = self.symbolicEngine.createSymbolicExpression(inst, node3, dst3.getRegister(),   "POPF AF operation");
    //         let expr4  = self.symbolicEngine.createSymbolicExpression(inst, node4, dst4.getRegister(),   "POPF ZF operation");
    //         let expr5  = self.symbolicEngine.createSymbolicExpression(inst, node5, dst5.getRegister(),   "POPF SF operation");
    //         let expr6  = self.symbolicEngine.createSymbolicExpression(inst, node6, dst6.getRegister(),   "POPF TF operation");
    //         let expr7  = self.symbolicEngine.createSymbolicExpression(inst, node7, dst7.getRegister(),   "POPF IF operation");
    //         let expr8  = self.symbolicEngine.createSymbolicExpression(inst, node8, dst8.getRegister(),   "POPF DF operation");
    //         let expr9  = self.symbolicEngine.createSymbolicExpression(inst, node9, dst9.getRegister(),   "POPF OF operation");
    //         let expr10 = self.symbolicEngine.createSymbolicExpression(inst, node10, dst10.getRegister(), "POPF NT operation");

    //         /* Spread taint */
    //         // expr1.isTainted  = self.taintEngine.taintAssignment(dst1, src);
    //         // expr2.isTainted  = self.taintEngine.taintAssignment(dst2, src);
    //         // expr3.isTainted  = self.taintEngine.taintAssignment(dst3, src);
    //         // expr4.isTainted  = self.taintEngine.taintAssignment(dst4, src);
    //         // expr5.isTainted  = self.taintEngine.taintAssignment(dst5, src);
    //         // expr6.isTainted  = self.taintEngine.taintAssignment(dst6, src);
    //         // expr7.isTainted  = self.taintEngine.taintAssignment(dst7, src);
    //         // expr8.isTainted  = self.taintEngine.taintAssignment(dst8, src);
    //         // expr9.isTainted  = self.taintEngine.taintAssignment(dst9, src);
    //         // expr10.isTainted = self.taintEngine.taintAssignment(dst10, src);

    //         /* Create the semantics - side effect */
    //         alignAddStack_s(inst, src.getSize());

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn popfd_s(&mut self, inst: x86Instruction) {
    //         let  stack      = self.architecture.get_stack_pointer();
    //         let  stackValue = self.architecture.getConcreteRegisterValue(stack) as u64;
    //         let  dst1       = Operand::Register(Register::CF);
    //         let  dst2       = Operand::Register(Register::PF);
    //         let  dst3       = Operand::Register(Register::AF);
    //         let  dst4       = Operand::Register(Register::ZF);
    //         let  dst5       = Operand::Register(Register::SF);
    //         let  dst6       = Operand::Register(Register::TF);
    //         let  dst7       = Operand::Register(Register::IF);
    //         let  dst8       = Operand::Register(Register::DF);
    //         let  dst9       = Operand::Register(Register::OF);
    //         let  dst10      = Operand::Register(Register::NT);
    //         let  dst11      = Operand::Register(Register::RF);
    //         let  dst12      = Operand::Register(Register::AC);
    //         let  dst13      = Operand::Register(Register::ID);
    //         let  src        = Operand::Memory(MemoryAccess::new(stackValue, stack.getSize()));

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node1  = self.ast_ctxt.extract(0,  0,  op1);
    //         let node2  = self.ast_ctxt.extract(2,  2,  op1);
    //         let node3  = self.ast_ctxt.extract(4,  4,  op1);
    //         let node4  = self.ast_ctxt.extract(6,  6,  op1);
    //         let node5  = self.ast_ctxt.extract(7,  7,  op1);
    //         let node6  = self.ast_ctxt.extract(8,  8,  op1);
    //         let node7  = self.ast_ctxt.bvtrue(); /* IF true? */
    //         let node8  = self.ast_ctxt.extract(10, 10, op1);
    //         let node9  = self.ast_ctxt.extract(11, 11, op1);
    //         /* IOPL don't support */
    //         let node10 = self.ast_ctxt.extract(14, 14, op1);
    //         let node11 = self.ast_ctxt.bvfalse(); /* RF clear */
    //         /* VM not changed */
    //         let node12 = self.ast_ctxt.extract(18, 18, op1);
    //         /* VIP not changed */
    //         /* VIF not changed */
    //         let node13 = self.ast_ctxt.extract(21, 21, op1);

    //         /* Create symbolic expression */
    //         let expr1  = self.symbolicEngine.createSymbolicExpression(inst, node1, dst1.getRegister(),   "POPFD CF operation");
    //         let expr2  = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2.getRegister(),   "POPFD PF operation");
    //         let expr3  = self.symbolicEngine.createSymbolicExpression(inst, node3, dst3.getRegister(),   "POPFD AF operation");
    //         let expr4  = self.symbolicEngine.createSymbolicExpression(inst, node4, dst4.getRegister(),   "POPFD ZF operation");
    //         let expr5  = self.symbolicEngine.createSymbolicExpression(inst, node5, dst5.getRegister(),   "POPFD SF operation");
    //         let expr6  = self.symbolicEngine.createSymbolicExpression(inst, node6, dst6.getRegister(),   "POPFD TF operation");
    //         let expr7  = self.symbolicEngine.createSymbolicExpression(inst, node7, dst7.getRegister(),   "POPFD IF operation");
    //         let expr8  = self.symbolicEngine.createSymbolicExpression(inst, node8, dst8.getRegister(),   "POPFD DF operation");
    //         let expr9  = self.symbolicEngine.createSymbolicExpression(inst, node9, dst9.getRegister(),   "POPFD OF operation");
    //         let expr10 = self.symbolicEngine.createSymbolicExpression(inst, node10, dst10.getRegister(), "POPFD NT operation");
    //         let expr11 = self.symbolicEngine.createSymbolicExpression(inst, node11, dst11.getRegister(), "POPFD RF operation");
    //         let expr12 = self.symbolicEngine.createSymbolicExpression(inst, node12, dst12.getRegister(), "POPFD AC operation");
    //         let expr13 = self.symbolicEngine.createSymbolicExpression(inst, node13, dst13.getRegister(), "POPFD ID operation");

    //         /* Spread taint */
    //         // expr1.isTainted  = self.taintEngine.taintAssignment(dst1, src);
    //         // expr2.isTainted  = self.taintEngine.taintAssignment(dst2, src);
    //         // expr3.isTainted  = self.taintEngine.taintAssignment(dst3, src);
    //         // expr4.isTainted  = self.taintEngine.taintAssignment(dst4, src);
    //         // expr5.isTainted  = self.taintEngine.taintAssignment(dst5, src);
    //         // expr6.isTainted  = self.taintEngine.taintAssignment(dst6, src);
    //         // expr7.isTainted  = self.taintEngine.taintAssignment(dst7, src);
    //         // expr8.isTainted  = self.taintEngine.taintAssignment(dst8, src);
    //         // expr9.isTainted  = self.taintEngine.taintAssignment(dst9, src);
    //         // expr10.isTainted = self.taintEngine.taintAssignment(dst10, src);
    //         // expr11.isTainted = self.taintEngine.taintAssignment(dst11, src);
    //         // expr12.isTainted = self.taintEngine.taintAssignment(dst12, src);
    //         // expr13.isTainted = self.taintEngine.taintAssignment(dst13, src);

    //         /* Create the semantics - side effect */
    //         alignAddStack_s(inst, src.getSize());

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn popfq_s(&mut self, inst: x86Instruction) {
    //         let  stack      = self.architecture.get_stack_pointer();
    //         let  stackValue = self.architecture.getConcreteRegisterValue(stack) as u64;
    //         let  dst1       = Operand::Register(Register::CF);
    //         let  dst2       = Operand::Register(Register::PF);
    //         let  dst3       = Operand::Register(Register::AF);
    //         let  dst4       = Operand::Register(Register::ZF);
    //         let  dst5       = Operand::Register(Register::SF);
    //         let  dst6       = Operand::Register(Register::TF);
    //         let  dst7       = Operand::Register(Register::IF);
    //         let  dst8       = Operand::Register(Register::DF);
    //         let  dst9       = Operand::Register(Register::OF);
    //         let  dst10      = Operand::Register(Register::NT);
    //         let  dst11      = Operand::Register(Register::RF);
    //         let  dst12      = Operand::Register(Register::AC);
    //         let  dst13      = Operand::Register(Register::ID);
    //         let  src        = Operand::Memory(MemoryAccess::new(stackValue, stack.getSize()));

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node1  = self.ast_ctxt.extract(0,  0,  op1);
    //         let node2  = self.ast_ctxt.extract(2,  2,  op1);
    //         let node3  = self.ast_ctxt.extract(4,  4,  op1);
    //         let node4  = self.ast_ctxt.extract(6,  6,  op1);
    //         let node5  = self.ast_ctxt.extract(7,  7,  op1);
    //         let node6  = self.ast_ctxt.extract(8,  8,  op1);
    //         let node7  = self.ast_ctxt.bvtrue(); /* IF true? */
    //         let node8  = self.ast_ctxt.extract(10, 10, op1);
    //         let node9  = self.ast_ctxt.extract(11, 11, op1);
    //         /* IOPL don't support */
    //         let node10 = self.ast_ctxt.extract(14, 14, op1);
    //         let node11 = self.ast_ctxt.bvfalse(); /* RF clear */
    //         /* VM not changed */
    //         let node12 = self.ast_ctxt.extract(18, 18, op1);
    //         /* VIP not changed */
    //         /* VIF not changed */
    //         let node13 = self.ast_ctxt.extract(21, 21, op1);

    //         /* Create symbolic expression */
    //         let expr1  = self.symbolicEngine.createSymbolicExpression(inst, node1, dst1.getRegister(),   "POPFQ CF operation");
    //         let expr2  = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2.getRegister(),   "POPFQ PF operation");
    //         let expr3  = self.symbolicEngine.createSymbolicExpression(inst, node3, dst3.getRegister(),   "POPFQ AF operation");
    //         let expr4  = self.symbolicEngine.createSymbolicExpression(inst, node4, dst4.getRegister(),   "POPFQ ZF operation");
    //         let expr5  = self.symbolicEngine.createSymbolicExpression(inst, node5, dst5.getRegister(),   "POPFQ SF operation");
    //         let expr6  = self.symbolicEngine.createSymbolicExpression(inst, node6, dst6.getRegister(),   "POPFQ TF operation");
    //         let expr7  = self.symbolicEngine.createSymbolicExpression(inst, node7, dst7.getRegister(),   "POPFQ IF operation");
    //         let expr8  = self.symbolicEngine.createSymbolicExpression(inst, node8, dst8.getRegister(),   "POPFQ DF operation");
    //         let expr9  = self.symbolicEngine.createSymbolicExpression(inst, node9, dst9.getRegister(),   "POPFQ OF operation");
    //         let expr10 = self.symbolicEngine.createSymbolicExpression(inst, node10, dst10.getRegister(), "POPFD NT operation");
    //         let expr11 = self.symbolicEngine.createSymbolicExpression(inst, node11, dst11.getRegister(), "POPFD RF operation");
    //         let expr12 = self.symbolicEngine.createSymbolicExpression(inst, node12, dst12.getRegister(), "POPFD AC operation");
    //         let expr13 = self.symbolicEngine.createSymbolicExpression(inst, node13, dst13.getRegister(), "POPFD ID operation");

    //         /* Spread taint */
    //         // expr1.isTainted  = self.taintEngine.taintAssignment(dst1, src);
    //         // expr2.isTainted  = self.taintEngine.taintAssignment(dst2, src);
    //         // expr3.isTainted  = self.taintEngine.taintAssignment(dst3, src);
    //         // expr4.isTainted  = self.taintEngine.taintAssignment(dst4, src);
    //         // expr5.isTainted  = self.taintEngine.taintAssignment(dst5, src);
    //         // expr6.isTainted  = self.taintEngine.taintAssignment(dst6, src);
    //         // expr7.isTainted  = self.taintEngine.taintAssignment(dst7, src);
    //         // expr8.isTainted  = self.taintEngine.taintAssignment(dst8, src);
    //         // expr9.isTainted  = self.taintEngine.taintAssignment(dst9, src);
    //         // expr10.isTainted = self.taintEngine.taintAssignment(dst10, src);
    //         // expr11.isTainted = self.taintEngine.taintAssignment(dst11, src);
    //         // expr12.isTainted = self.taintEngine.taintAssignment(dst12, src);
    //         // expr13.isTainted = self.taintEngine.taintAssignment(dst13, src);

    //         /* Create the semantics - side effect */
    //         alignAddStack_s(inst, src.getSize());

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn por_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "POR operation");

    //         /* Update the x87 FPU Tag Word */
    //         self.updateFTW(inst, expr);

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn prefetchx_s(&mut self, inst: x86Instruction) {
    //         let src = inst.operands[0];

    //         /* Only specify that the instruction performs an implicit memory read */
    //         self.symbolicEngine.getOperandAst(inst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pshufb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         let mut pack: Vec<Instruction> = Vec::new();
    //         pack.reserve(dst.getSize());

    //         /* Create the semantics */
    //         let mut i = dst.get_bit_size();
    //         while i > 0 {
    //           i -= 8;
    //           let control = i+7;
    //           let index_low = i;
    //           let index_high = i+(if dst.getSize() == 8 {2} else {3});
    //           pack.push(
    //             self.ast_ctxt.bvmul(
    //               self.ast_ctxt.zx(BitSizes::BYTE-1, self.ast_ctxt.bvnot(
    //                 self.ast_ctxt.extract(control, control, op2))),
    //               self.ast_ctxt.extract(BitSizes::BYTE-1, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op1,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(BitSizes::DQWORD-(index_high-index_low)-1,
    //                       self.ast_ctxt.extract(index_high, index_low, op2)),
    //                     self.ast_ctxt.bv(8, BitSizes::DQWORD))))));
    //         }

    //         let node = self.ast_ctxt.concat(pack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSHUFD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pshufd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let ord = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, ord);

    //         /* Create the semantics */
    //         let mut pack: Vec<Instruction> = Vec::new();
    //         pack.reserve(4);

    //         pack.push(
    //           self.ast_ctxt.extract(31, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(7, 6, op3)),
    //                 self.ast_ctxt.bv(32, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(31, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(5, 4, op3)),
    //                 self.ast_ctxt.bv(32, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(31, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(3, 2, op3)),
    //                 self.ast_ctxt.bv(32, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(31, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(1, 0, op3)),
    //                 self.ast_ctxt.bv(32, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );

    //         let node = self.ast_ctxt.concat(pack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSHUFD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pshufhw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let ord = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, ord);

    //         /* Create the semantics */
    //         let mut pack: Vec<Instruction> = Vec::new();
    //         pack.reserve(5);

    //         pack.push(
    //           self.ast_ctxt.extract(79, 64,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(7, 6, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(79, 64,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(5, 4, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(79, 64,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(3, 2, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(79, 64,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(1, 0, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(63, 0, op2)
    //         );

    //         let node = self.ast_ctxt.concat(pack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSHUFHW operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pshuflw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let ord = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, ord);

    //         /* Create the semantics */
    //         let mut pack: Vec<Instruction> = Vec::new();
    //         pack.reserve(5);

    //         pack.push(
    //           self.ast_ctxt.extract(127, 64, op2)
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(15, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(7, 6, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(15, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(5, 4, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(15, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(3, 2, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(15, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::DQWORD-2, self.ast_ctxt.extract(1, 0, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::DQWORD)
    //               )
    //             )
    //           )
    //         );

    //         let node = self.ast_ctxt.concat(pack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSHUFLW operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pshufw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];
    //         let ord = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, ord);

    //         /* Create the semantics */
    //         let mut pack: Vec<Instruction> = Vec::new();
    //         pack.reserve(4);

    //         pack.push(
    //           self.ast_ctxt.extract(15, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::QWORD-2, self.ast_ctxt.extract(7, 6, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::QWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(15, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::QWORD-2, self.ast_ctxt.extract(5, 4, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::QWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(15, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::QWORD-2, self.ast_ctxt.extract(3, 2, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::QWORD)
    //               )
    //             )
    //           )
    //         );
    //         pack.push(
    //           self.ast_ctxt.extract(15, 0,
    //             self.ast_ctxt.bvlshr(
    //               op2,
    //               self.ast_ctxt.bvmul(
    //                 self.ast_ctxt.zx(BitSizes::QWORD-2, self.ast_ctxt.extract(1, 0, op3)),
    //                 self.ast_ctxt.bv(16, BitSizes::QWORD)
    //               )
    //             )
    //           )
    //         );

    //         let node = self.ast_ctxt.concat(pack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSHUFW operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pslld_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(4);

    //         match dst.get_bit_size() {
    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(127, 96, op1), self.ast_ctxt.extract(31, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract( 95, 64, op1), self.ast_ctxt.extract(31, 0, op2)));

    //             // todo: duplicated below
    //                         packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(63, 32, op1), self.ast_ctxt.extract(31, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(31,  0, op1), self.ast_ctxt.extract(31, 0, op2)));

    // }
    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(63, 32, op1), self.ast_ctxt.extract(31, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(31,  0, op1), self.ast_ctxt.extract(31, 0, op2)));
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::pslld_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSLLD operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pslldq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvshl(
    //                       op1,
    //                       self.ast_ctxt.bvmul(
    //                         self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::WORD, dst.get_bit_size())),
    //                           self.ast_ctxt.bv(BitSizes::WORD, dst.get_bit_size()),
    //                           op2
    //                         ),
    //                         self.ast_ctxt.bv(ByteSizes::QWORD, dst.get_bit_size())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSLLDQ operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psllq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let mut node: Instruction;

    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(2);

    //         match dst.get_bit_size() {
    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(127, 64, op1), self.ast_ctxt.extract(63, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract( 63,  0, op1), self.ast_ctxt.extract(63, 0, op2)));
    //             node = self.ast_ctxt.concat(packed);
    //           }

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             /* MMX register is only one QWORD so it's a simple shl */
    //             node = self.ast_ctxt.bvshl(op1, op2);
    //           }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::psllq_s(): Invalid operand size.");"#),
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSLLQ operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psllw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(8);

    //         match (dst.get_bit_size()) {
    //           /* XMM */
    //         BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(127, 112, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(111,  96, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract( 95,  80, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract( 79,  64, op1), self.ast_ctxt.extract(15, 0, op2)));

    //             // todo: duplicated below
    //                packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(63, 48, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(47, 32, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(31, 16, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(15,  0, op1), self.ast_ctxt.extract(15, 0, op2)));
    //         }
    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(63, 48, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(47, 32, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(31, 16, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(15,  0, op1), self.ast_ctxt.extract(15, 0, op2)));
    //         }

    //         _ =>
    //             {todo!(r#"triton::exceptions::Semantics("x86Semantics::psllw_s(): Invalid operand size.");"#);}
    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSLLW operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psrad_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         let shift = self.ast_ctxt.ite(
    //           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::DWORD, src.get_bit_size())),
    //           self.ast_ctxt.bv(BitSizes::DWORD, src.get_bit_size()),
    //           op2
    //         );

    //         if (shift.getBitvectorSize() < BitSizes::DWORD) {
    //           shift = self.ast_ctxt.zx(BitSizes::DWORD - shift.getBitvectorSize(), shift);
    //         }
    //         else {
    //           shift = self.ast_ctxt.extract(BitSizes::DWORD - 1, 0, shift);
    //         }

    //         for i in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (i * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.bvashr(self.ast_ctxt.extract(high, low, op1), shift));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSRAD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psraw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         let shift = self.ast_ctxt.ite(
    //           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::WORD, src.get_bit_size())),
    //           self.ast_ctxt.bv(BitSizes::WORD, src.get_bit_size()),
    //           op2
    //         );

    //         if (shift.getBitvectorSize() < BitSizes::WORD) {
    //           shift = self.ast_ctxt.zx(BitSizes::WORD - shift.getBitvectorSize(), shift);
    //         }
    //         else {
    //           shift = self.ast_ctxt.extract(BitSizes::WORD - 1, 0, shift);
    //         }

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.bvashr(self.ast_ctxt.extract(high, low, op1), shift));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSRAW operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psrld_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(4);

    //         match dst.get_bit_size() {
    //           /* XMM */
    //         BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(127, 96, op1), self.ast_ctxt.extract(31, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract( 95, 64, op1), self.ast_ctxt.extract(31, 0, op2)));

    //             // todo: duplicated below
    //                         packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(63, 32, op1), self.ast_ctxt.extract(31, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(31,  0, op1), self.ast_ctxt.extract(31, 0, op2)));

    // }
    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(63, 32, op1), self.ast_ctxt.extract(31, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(31,  0, op1), self.ast_ctxt.extract(31, 0, op2)));
    //         }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::psrld_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSRLD operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psrldq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvlshr(
    //                       op1,
    //                       self.ast_ctxt.bvmul(
    //                         self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::WORD, dst.get_bit_size())),
    //                           self.ast_ctxt.bv(BitSizes::WORD, dst.get_bit_size()),
    //                           op2
    //                         ),
    //                         self.ast_ctxt.bv(ByteSizes::QWORD, dst.get_bit_size())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSRLDQ operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psrlq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let mut node: Instruction;

    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(2);

    //         match dst.get_bit_size() {
    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(127, 64, op1), self.ast_ctxt.extract(63, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract( 63,  0, op1), self.ast_ctxt.extract(63, 0, op2)));
    //             node = self.ast_ctxt.concat(packed);
    //             }

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             /* MMX register is only one QWORD so it's a simple shr */
    //             node = self.ast_ctxt.bvlshr(op1, op2);
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::psrlq_s(): Invalid operand size.");"#),
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSRLQ operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psrlw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(8);

    //         match dst.get_bit_size() {
    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(127, 112, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(111,  96, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract( 95,  80, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract( 79,  64, op1), self.ast_ctxt.extract(15, 0, op2)));

    //             // todo: duplicated below
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(63, 48, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(47, 32, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(31, 16, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(15,  0, op1), self.ast_ctxt.extract(15, 0, op2)));

    // }
    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(63, 48, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(47, 32, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(31, 16, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             packed.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(15,  0, op1), self.ast_ctxt.extract(15, 0, op2)));
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::psrlw_s(): Invalid operand size.");"#);
    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSRLW operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psubb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(16);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(127, 120, op1), self.ast_ctxt.extract(127, 120, op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(119, 112, op1), self.ast_ctxt.extract(119, 112, op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(111, 104, op1), self.ast_ctxt.extract(111, 104, op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(103, 96,  op1), self.ast_ctxt.extract(103, 96,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(95,  88,  op1), self.ast_ctxt.extract(95,  88,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(87,  80,  op1), self.ast_ctxt.extract(87,  80,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(79,  72,  op1), self.ast_ctxt.extract(79,  72,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(71,  64,  op1), self.ast_ctxt.extract(71,  64,  op2)));

    //             // todo: duplicated below
    //                         packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(63,  56,  op1), self.ast_ctxt.extract(63,  56,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(55,  48,  op1), self.ast_ctxt.extract(55,  48,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(47,  40,  op1), self.ast_ctxt.extract(47,  40,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(39,  32,  op1), self.ast_ctxt.extract(39,  32,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(31,  24,  op1), self.ast_ctxt.extract(31,  24,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(23,  16,  op1), self.ast_ctxt.extract(23,  16,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(15,  8,   op1), self.ast_ctxt.extract(15,  8,   op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(7,   0,   op1), self.ast_ctxt.extract(7,   0,   op2)));
    // }

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(63,  56,  op1), self.ast_ctxt.extract(63,  56,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(55,  48,  op1), self.ast_ctxt.extract(55,  48,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(47,  40,  op1), self.ast_ctxt.extract(47,  40,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(39,  32,  op1), self.ast_ctxt.extract(39,  32,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(31,  24,  op1), self.ast_ctxt.extract(31,  24,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(23,  16,  op1), self.ast_ctxt.extract(23,  16,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(15,  8,   op1), self.ast_ctxt.extract(15,  8,   op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(7,   0,   op1), self.ast_ctxt.extract(7,   0,   op2)));
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::psubb_s(): Invalid operand size.");"#),

    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSUBB operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psubd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(4);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(127, 96, op1), self.ast_ctxt.extract(127, 96, op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(95,  64, op1), self.ast_ctxt.extract(95,  64, op2)));

    //             // todo: duplicated below
    //                         packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(63,  32, op1), self.ast_ctxt.extract(63,  32, op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(31,  0,  op1), self.ast_ctxt.extract(31,  0,  op2)));
    // }

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(63,  32, op1), self.ast_ctxt.extract(63,  32, op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(31,  0,  op1), self.ast_ctxt.extract(31,  0,  op2)));
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::psubd_s(): Invalid operand size.");"#),

    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSUBD operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psubq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(2);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(127, 64, op1), self.ast_ctxt.extract(127, 64, op2)));

    //             // todo: duplicated below
    //                         packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(63,  0,  op1), self.ast_ctxt.extract(63,  0,  op2)));
    //           }

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(63,  0,  op1), self.ast_ctxt.extract(63,  0,  op2)));
    //           }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::psubq_s(): Invalid operand size.");"#),

    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSUBQ operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn psubw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut packed: Vec<Instruction> = Vec::new();
    //         packed.reserve(8);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(127, 112, op1), self.ast_ctxt.extract(127, 112, op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(111, 96,  op1), self.ast_ctxt.extract(111, 96,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(95,  80,  op1), self.ast_ctxt.extract(95,  80,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(79,  64,  op1), self.ast_ctxt.extract(79,  64,  op2)));

    //             // todo: duplicated below
    //                         packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(63,  48,  op1), self.ast_ctxt.extract(63,  48,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(47,  32,  op1), self.ast_ctxt.extract(47,  32,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(31,  16,  op1), self.ast_ctxt.extract(31,  16,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(15,  0,   op1), self.ast_ctxt.extract(15,  0,   op2)));

    // }
    //           /* MMX */
    //         BitSizes::QWORD => {
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(63,  48,  op1), self.ast_ctxt.extract(63,  48,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(47,  32,  op1), self.ast_ctxt.extract(47,  32,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(31,  16,  op1), self.ast_ctxt.extract(31,  16,  op2)));
    //             packed.push(self.ast_ctxt.bvsub(self.ast_ctxt.extract(15,  0,   op1), self.ast_ctxt.extract(15,  0,   op2)));
    //             }

    //            _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::psubw_s(): Invalid operand size.");"#),

    //         }

    //         let node = self.ast_ctxt.concat(packed);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PSUBW operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn ptest_s(&mut self, inst: x86Instruction) {
    //         let src1 = inst.operands[0];
    //         let src2 = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvand(op1, op2);
    //         let node2 = self.ast_ctxt.bvand(op1, self.ast_ctxt.bvnot(op2));

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "PTEST operation");
    //         let expr2 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node2, "PTEST operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2);
    //         // // expr2.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2);

    //         /* Update symbolic flags */
    //         self.clearFlag_s(inst, Register::AF, "Clears adjust flag");
    //         self.cfPtest_s(inst, expr2, src1, ); // todo: vol = true
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.clearFlag_s(inst, Register::PF, "Clears parity flag");
    //         self.clearFlag_s(inst, Register::SF, "Clears sign flag");
    //         self.zf_s(inst, expr1, src1, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn punpckhbw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(24);

    //         match dst.get_bit_size() {

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             unpack.push(self.ast_ctxt.extract(63, 56, op2));
    //             unpack.push(self.ast_ctxt.extract(63, 56, op1));
    //             unpack.push(self.ast_ctxt.extract(55, 48, op2));
    //             unpack.push(self.ast_ctxt.extract(55, 48, op1));
    //             unpack.push(self.ast_ctxt.extract(47, 40, op2));
    //             unpack.push(self.ast_ctxt.extract(55, 40, op1));
    //             unpack.push(self.ast_ctxt.extract(39, 32, op2));
    //             unpack.push(self.ast_ctxt.extract(39, 32, op1));
    //             }

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             unpack.push(self.ast_ctxt.extract(127, 120, op2));
    //             unpack.push(self.ast_ctxt.extract(127, 120, op1));
    //             unpack.push(self.ast_ctxt.extract(119, 112, op2));
    //             unpack.push(self.ast_ctxt.extract(119, 112, op1));
    //             unpack.push(self.ast_ctxt.extract(111, 104, op2));
    //             unpack.push(self.ast_ctxt.extract(111, 104, op1));
    //             unpack.push(self.ast_ctxt.extract(103, 96,  op2));
    //             unpack.push(self.ast_ctxt.extract(103, 96,  op1));
    //             unpack.push(self.ast_ctxt.extract(95,  88,  op2));
    //             unpack.push(self.ast_ctxt.extract(95,  88,  op1));
    //             unpack.push(self.ast_ctxt.extract(87,  80,  op2));
    //             unpack.push(self.ast_ctxt.extract(87,  80,  op1));
    //             unpack.push(self.ast_ctxt.extract(79,  72,  op2));
    //             unpack.push(self.ast_ctxt.extract(79,  72,  op1));
    //             unpack.push(self.ast_ctxt.extract(71,  64,  op2));
    //             unpack.push(self.ast_ctxt.extract(71,  64,  op1));
    //         }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::punpckhbw_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUNPCKHBW operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn punpckhdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(6);

    //         match dst.get_bit_size() {

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             unpack.push(self.ast_ctxt.extract(63, 32, op2));
    //             unpack.push(self.ast_ctxt.extract(63, 32, op1));
    //             }

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             unpack.push(self.ast_ctxt.extract(127, 96, op2));
    //             unpack.push(self.ast_ctxt.extract(127, 96, op1));
    //             unpack.push(self.ast_ctxt.extract(95,  64, op2));
    //             unpack.push(self.ast_ctxt.extract(95,  64, op1));
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::punpckhdq_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUNPCKHDQ operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn punpckhqdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(2);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             unpack.push(self.ast_ctxt.extract(127, 64, op2));
    //             unpack.push(self.ast_ctxt.extract(127, 64, op1));
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::punpckhqdq_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUNPCKHQDQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn punpckhwd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(12);

    //         match dst.get_bit_size() {

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             unpack.push(self.ast_ctxt.extract(63, 48, op2));
    //             unpack.push(self.ast_ctxt.extract(63, 48, op1));
    //             unpack.push(self.ast_ctxt.extract(47, 32, op2));
    //             unpack.push(self.ast_ctxt.extract(47, 32, op1));
    //           }

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             unpack.push(self.ast_ctxt.extract(127, 112, op2));
    //             unpack.push(self.ast_ctxt.extract(127, 112, op1));
    //             unpack.push(self.ast_ctxt.extract(111, 96,  op2));
    //             unpack.push(self.ast_ctxt.extract(111, 96,  op1));
    //             unpack.push(self.ast_ctxt.extract(95,  80,  op2));
    //             unpack.push(self.ast_ctxt.extract(95,  80,  op1));
    //             unpack.push(self.ast_ctxt.extract(79,  64,  op2));
    //             unpack.push(self.ast_ctxt.extract(79,  64,  op1));
    //           }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::punpckhwd_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUNPCKHWD operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn punpcklbw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(24);

    //         match dst.get_bit_size() {

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             unpack.push(self.ast_ctxt.extract(31, 24, op2));
    //             unpack.push(self.ast_ctxt.extract(31, 24, op1));
    //             unpack.push(self.ast_ctxt.extract(23, 16, op2));
    //             unpack.push(self.ast_ctxt.extract(23, 16, op1));
    //             unpack.push(self.ast_ctxt.extract(15, 8,  op2));
    //             unpack.push(self.ast_ctxt.extract(15, 8,  op1));
    //             unpack.push(self.ast_ctxt.extract(7,  0,  op2));
    //             unpack.push(self.ast_ctxt.extract(7,  0,  op1));
    //           }

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             unpack.push(self.ast_ctxt.extract(63, 56, op2));
    //             unpack.push(self.ast_ctxt.extract(63, 56, op1));
    //             unpack.push(self.ast_ctxt.extract(55, 48, op2));
    //             unpack.push(self.ast_ctxt.extract(55, 48, op1));
    //             unpack.push(self.ast_ctxt.extract(47, 40, op2));
    //             unpack.push(self.ast_ctxt.extract(47, 40, op1));
    //             unpack.push(self.ast_ctxt.extract(39, 32, op2));
    //             unpack.push(self.ast_ctxt.extract(39, 32, op1));
    //             unpack.push(self.ast_ctxt.extract(31, 24, op2));
    //             unpack.push(self.ast_ctxt.extract(31, 24, op1));
    //             unpack.push(self.ast_ctxt.extract(23, 16, op2));
    //             unpack.push(self.ast_ctxt.extract(23, 16, op1));
    //             unpack.push(self.ast_ctxt.extract(15, 8,  op2));
    //             unpack.push(self.ast_ctxt.extract(15, 8,  op1));
    //             unpack.push(self.ast_ctxt.extract(7,  0,  op2));
    //             unpack.push(self.ast_ctxt.extract(7,  0,  op1));
    //           }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::punpcklbw_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUNPCKLBW operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn punpckldq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(6);

    //         match dst.get_bit_size() {

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             unpack.push(self.ast_ctxt.extract(31, 0, op2));
    //             unpack.push(self.ast_ctxt.extract(31, 0, op1));
    //           }

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             unpack.push(self.ast_ctxt.extract(63, 32, op2));
    //             unpack.push(self.ast_ctxt.extract(63, 32, op1));
    //             unpack.push(self.ast_ctxt.extract(31, 0,  op2));
    //             unpack.push(self.ast_ctxt.extract(31, 0,  op1));
    //           }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::punpckldq_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUNPCKLDQ operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn punpcklqdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(2);

    //         match dst.get_bit_size() {

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             unpack.push(self.ast_ctxt.extract(63, 0, op2));
    //             unpack.push(self.ast_ctxt.extract(63, 0, op1));
    //           }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::punpcklqdq_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUNPCKLQDQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn punpcklwd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(12);

    //         match dst.get_bit_size() {

    //           /* MMX */
    //           BitSizes::QWORD => {
    //             unpack.push(self.ast_ctxt.extract(31, 16, op2));
    //             unpack.push(self.ast_ctxt.extract(31, 16, op1));
    //             unpack.push(self.ast_ctxt.extract(15, 0,  op2));
    //             unpack.push(self.ast_ctxt.extract(15, 0,  op1));
    //           }

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             unpack.push(self.ast_ctxt.extract(63, 48, op2));
    //             unpack.push(self.ast_ctxt.extract(63, 48, op1));
    //             unpack.push(self.ast_ctxt.extract(47, 32, op2));
    //             unpack.push(self.ast_ctxt.extract(47, 32, op1));
    //             unpack.push(self.ast_ctxt.extract(31, 16, op2));
    //             unpack.push(self.ast_ctxt.extract(31, 16, op1));
    //             unpack.push(self.ast_ctxt.extract(15, 0,  op2));
    //             unpack.push(self.ast_ctxt.extract(15, 0,  op1));
    //           }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::punpcklwd_s(): Invalid operand size.");"#),
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUNPCKLWD operation");

    //         /* Update the x87 FPU Tag Word */
    //         if (dst.get_bit_size() == BitSizes::QWORD) {
    //           self.updateFTW(inst, expr);
    //         }

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn push_s(&mut self, inst: x86Instruction) {
    //         let src           = inst.operands[0];
    //         let stack          = self.architecture.get_stack_pointer();
    //         let mut size: u32 = stack.getSize();

    //         /* If it's an immediate source, the memory access is always based on the arch size */
    //         if (src.getType() != triton::arch::OP_IMM){
    //           size = src.getSize();
    // }
    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics - side effect */
    //         let  stackValue = alignSubStack_s(inst, size);
    //         let  dst        = Operand::Memory(MemoryAccess::new(stackValue, size));

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), op1);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUSH operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pushal_s(&mut self, inst: x86Instruction) {
    //         let stack      = self.architecture.get_stack_pointer();
    //         let stackValue = self.architecture.getConcreteRegisterValue(stack) as u64;
    //         let dst1       = Operand::Memory(MemoryAccess::new(stackValue-(stack.getSize() * 1), stack.getSize()));
    //         let dst2       = Operand::Memory(MemoryAccess::new(stackValue-(stack.getSize() * 2), stack.getSize()));
    //         let dst3       = Operand::Memory(MemoryAccess::new(stackValue-(stack.getSize() * 3), stack.getSize()));
    //         let dst4       = Operand::Memory(MemoryAccess::new(stackValue-(stack.getSize() * 4), stack.getSize()));
    //         let dst5       = Operand::Memory(MemoryAccess::new(stackValue-(stack.getSize() * 5), stack.getSize()));
    //         let dst6       = Operand::Memory(MemoryAccess::new(stackValue-(stack.getSize() * 6), stack.getSize()));
    //         let dst7       = Operand::Memory(MemoryAccess::new(stackValue-(stack.getSize() * 7), stack.getSize()));
    //         let dst8       = Operand::Memory(MemoryAccess::new(stackValue-(stack.getSize() * 8), stack.getSize()));
    //         let src1       = Operand::Register(Register::EAX);
    //         let src2       = Operand::Register(Register::ECX);
    //         let src3       = Operand::Register(Register::EDX);
    //         let src4       = Operand::Register(Register::EBX);
    //         let src5       = Operand::Register(Register::ESP);
    //         let src6       = Operand::Register(Register::EBP);
    //         let src7       = Operand::Register(Register::ESI);
    //         let src8       = Operand::Register(Register::EDI);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src3);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, src4);
    //         let op5 = self.symbolicEngine.getOperandAst(inst, src5);
    //         let op6 = self.symbolicEngine.getOperandAst(inst, src6);
    //         let op7 = self.symbolicEngine.getOperandAst(inst, src7);
    //         let op8 = self.symbolicEngine.getOperandAst(inst, src8);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.zx(dst1.get_bit_size() - src1.get_bit_size(), op1);
    //         let node2 = self.ast_ctxt.zx(dst2.get_bit_size() - src2.get_bit_size(), op2);
    //         let node3 = self.ast_ctxt.zx(dst3.get_bit_size() - src3.get_bit_size(), op3);
    //         let node4 = self.ast_ctxt.zx(dst4.get_bit_size() - src4.get_bit_size(), op4);
    //         let node5 = self.ast_ctxt.zx(dst5.get_bit_size() - src5.get_bit_size(), op5);
    //         let node6 = self.ast_ctxt.zx(dst6.get_bit_size() - src6.get_bit_size(), op6);
    //         let node7 = self.ast_ctxt.zx(dst7.get_bit_size() - src7.get_bit_size(), op7);
    //         let node8 = self.ast_ctxt.zx(dst8.get_bit_size() - src8.get_bit_size(), op8);

    //         /* Create symbolic expression */
    //         alignSubStack_s(inst, 32);
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst1, "PUSHAL EAX operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2, "PUSHAL ECX operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, dst3, "PUSHAL EDX operation");
    //         let expr4 = self.symbolicEngine.createSymbolicExpression(inst, node4, dst4, "PUSHAL EBX operation");
    //         let expr5 = self.symbolicEngine.createSymbolicExpression(inst, node5, dst5, "PUSHAL ESP operation");
    //         let expr6 = self.symbolicEngine.createSymbolicExpression(inst, node6, dst6, "PUSHAL EBP operation");
    //         let expr7 = self.symbolicEngine.createSymbolicExpression(inst, node7, dst7, "PUSHAL ESI operation");
    //         let expr8 = self.symbolicEngine.createSymbolicExpression(inst, node8, dst8, "PUSHAL EDI operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst1, src1);
    //         // expr2.isTainted = self.taintEngine.taintAssignment(dst2, src2);
    //         // expr3.isTainted = self.taintEngine.taintAssignment(dst3, src3);
    //         // expr4.isTainted = self.taintEngine.taintAssignment(dst4, src4);
    //         // expr5.isTainted = self.taintEngine.taintAssignment(dst5, src5);
    //         // expr6.isTainted = self.taintEngine.taintAssignment(dst6, src6);
    //         // expr7.isTainted = self.taintEngine.taintAssignment(dst7, src7);
    //         // expr8.isTainted = self.taintEngine.taintAssignment(dst8, src8);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pushfd_s(&mut self, inst: x86Instruction) {
    //         let stack = self.architecture.get_stack_pointer();

    //         /* Create the semantics - side effect */
    //         let stackValue = alignSubStack_s(inst, stack.getSize());
    //         let dst        = Operand::Memory(MemoryAccess::new(stackValue, stack.getSize()));
    //         let src1       = Operand::Register(Register::CF);
    //         let src2       = Operand::Register(Register::PF);
    //         let src3       = Operand::Register(Register::AF);
    //         let src4       = Operand::Register(Register::ZF);
    //         let src5       = Operand::Register(Register::SF);
    //         let src6       = Operand::Register(Register::TF);
    //         let src7       = Operand::Register(Register::IF);
    //         let src8       = Operand::Register(Register::DF);
    //         let src9       = Operand::Register(Register::OF);
    //         let src10      = Operand::Register(Register::NT);
    //         let src11      = Operand::Register(Register::AC);
    //         let src12      = Operand::Register(Register::VIF);
    //         let src13      = Operand::Register(Register::VIP);
    //         let src14      = Operand::Register(Register::ID);

    //         /* Create symbolic operands */
    //         let op1  = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2  = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3  = self.symbolicEngine.getOperandAst(inst, src3);
    //         let op4  = self.symbolicEngine.getOperandAst(inst, src4);
    //         let op5  = self.symbolicEngine.getOperandAst(inst, src5);
    //         let op6  = self.symbolicEngine.getOperandAst(inst, src6);
    //         let op7  = self.symbolicEngine.getOperandAst(inst, src7);
    //         let op8  = self.symbolicEngine.getOperandAst(inst, src8);
    //         let op9  = self.symbolicEngine.getOperandAst(inst, src9);
    //         let op10 = self.symbolicEngine.getOperandAst(inst, src10);
    //         let op11 = self.symbolicEngine.getOperandAst(inst, src11);
    //         let op12 = self.symbolicEngine.getOperandAst(inst, src12);
    //         let op13 = self.symbolicEngine.getOperandAst(inst, src13);
    //         let op14 = self.symbolicEngine.getOperandAst(inst, src14);

    //         /* Create the semantics */
    //         let mut eflags: Vec<Instruction> = Vec::new();
    //         eflags.reserve(22);

    //         eflags.push(op14);
    //         eflags.push(op13);
    //         eflags.push(op12);
    //         eflags.push(op11);
    //         eflags.push(self.ast_ctxt.bvfalse()); /* vm */
    //         eflags.push(self.ast_ctxt.bvfalse()); /* rf */
    //         eflags.push(self.ast_ctxt.bvfalse()); /* Reserved */
    //         eflags.push(op10);
    //         eflags.push(self.ast_ctxt.bvfalse()); /* iopl */
    //         eflags.push(self.ast_ctxt.bvfalse()); /* iopl */
    //         eflags.push(op9);
    //         eflags.push(op8);
    //         eflags.push(op7);
    //         eflags.push(op6);
    //         eflags.push(op5);
    //         eflags.push(op4);
    //         eflags.push(self.ast_ctxt.bvfalse()); /* Reserved */
    //         eflags.push(op3);
    //         eflags.push(self.ast_ctxt.bvfalse()); /* Reserved */
    //         eflags.push(op2);
    //         eflags.push(self.ast_ctxt.bvtrue()); /* Reserved */
    //         eflags.push(op1);

    //         let node = self.ast_ctxt.zx(
    //                       dst.get_bit_size() - eflags.size() as u32,
    //                       self.ast_ctxt.concat(eflags)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUSHFD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src2);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src3);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src4);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src5);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src6);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src7);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src8);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src9);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src10);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src11);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src12);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src13);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src14);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pushfq_s(&mut self, inst: x86Instruction) {
    //         let stack = self.architecture.get_stack_pointer();

    //         /* Create the semantics - side effect */
    //         let stackValue = alignSubStack_s(inst, stack.getSize());
    //         let dst        = Operand::Memory(MemoryAccess::new(stackValue, stack.getSize()));
    //         let src1       = Operand::Register(Register::CF);
    //         let src2       = Operand::Register(Register::PF);
    //         let src3       = Operand::Register(Register::AF);
    //         let src4       = Operand::Register(Register::ZF);
    //         let src5       = Operand::Register(Register::SF);
    //         let src6       = Operand::Register(Register::TF);
    //         let src7       = Operand::Register(Register::IF);
    //         let src8       = Operand::Register(Register::DF);
    //         let src9       = Operand::Register(Register::OF);
    //         let src10      = Operand::Register(Register::NT);
    //         let src11      = Operand::Register(Register::AC);
    //         let src12      = Operand::Register(Register::VIF);
    //         let src13      = Operand::Register(Register::VIP);
    //         let src14      = Operand::Register(Register::ID);

    //         /* Create symbolic operands */
    //         let op1  = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2  = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3  = self.symbolicEngine.getOperandAst(inst, src3);
    //         let op4  = self.symbolicEngine.getOperandAst(inst, src4);
    //         let op5  = self.symbolicEngine.getOperandAst(inst, src5);
    //         let op6  = self.symbolicEngine.getOperandAst(inst, src6);
    //         let op7  = self.symbolicEngine.getOperandAst(inst, src7);
    //         let op8  = self.symbolicEngine.getOperandAst(inst, src8);
    //         let op9  = self.symbolicEngine.getOperandAst(inst, src9);
    //         let op10 = self.symbolicEngine.getOperandAst(inst, src10);
    //         let op11 = self.symbolicEngine.getOperandAst(inst, src11);
    //         let op12 = self.symbolicEngine.getOperandAst(inst, src12);
    //         let op13 = self.symbolicEngine.getOperandAst(inst, src13);
    //         let op14 = self.symbolicEngine.getOperandAst(inst, src14);

    //         /* Create the semantics */
    //         let mut eflags: Vec<Instruction> = Vec::new();
    //         eflags.reserve(22);

    //         eflags.push(op14);
    //         eflags.push(op13);
    //         eflags.push(op12);
    //         eflags.push(op11);
    //         eflags.push(self.ast_ctxt.bvfalse()); /* vm */
    //         eflags.push(self.ast_ctxt.bvfalse()); /* rf */
    //         eflags.push(self.ast_ctxt.bvfalse()); /* Reserved */
    //         eflags.push(op10);
    //         eflags.push(self.ast_ctxt.bvfalse()); /* iopl */
    //         eflags.push(self.ast_ctxt.bvfalse()); /* iopl */
    //         eflags.push(op9);
    //         eflags.push(op8);
    //         eflags.push(op7);
    //         eflags.push(op6);
    //         eflags.push(op5);
    //         eflags.push(op4);
    //         eflags.push(self.ast_ctxt.bvfalse()); /* Reserved */
    //         eflags.push(op3);
    //         eflags.push(self.ast_ctxt.bvfalse()); /* Reserved */
    //         eflags.push(op2);
    //         eflags.push(self.ast_ctxt.bvtrue()); /* Reserved */
    //         eflags.push(op1);

    //         let node = self.ast_ctxt.zx(
    //                       dst.get_bit_size() - eflags.size() as u32,
    //                       self.ast_ctxt.concat(eflags)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PUSHFQ operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src2);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src3);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src4);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src5);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src6);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src7);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src8);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src9);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src10);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src11);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src12);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src13);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src14);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn pxor_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvxor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "PXOR operation");

    //         /* Update the x87 FPU Tag Word */
    //         self.updateFTW(inst, expr);

    //         /* Spread taint */
    //         // if (dst.getType() == OP_REG && src.getRegister() == dst.getRegister()){
    //         //   self.taintEngine.setTaint(src, false);
    //         // }else{
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // }
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn rcl_s(&mut self, inst: x86Instruction) {
    //         let dst   = inst.operands[0];
    //         let src   = inst.operands[1];
    //         let  srcCf = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1    = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2    = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2bis = self.symbolicEngine.getOperandAst(src);
    //         let op3    = self.symbolicEngine.getOperandAst(inst, srcCf);

    //         match dst.get_bit_size() {
    //           /* Mask: 0x1f without MOD */
    //           BitSizes::QWORD => {
    //             op2 = self.ast_ctxt.bvand(
    //                     op2,
    //                     self.ast_ctxt.bv(BitSizes::QWORD-1, src.get_bit_size())
    //                   );
    //             }

    //           /* Mask: 0x1f without MOD */
    //           BitSizes::DWORD => {
    //             op2 = self.ast_ctxt.bvand(
    //                     op2,
    //                     self.ast_ctxt.bv(BitSizes::DWORD-1, src.get_bit_size())
    //                   );
    //             }

    //           /* Mask: 0x1f MOD size + 1 */
    //           BitSizes::WORD | BitSizes::BYTE => {
    //             op2 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op2,
    //                       self.ast_ctxt.bv(BitSizes::DWORD-1, src.get_bit_size())),
    //                     self.ast_ctxt.bv(dst.get_bit_size()+1, src.get_bit_size())
    //                   );
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::rcl_s(): Invalid destination size");"#),
    //         }

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvrol(
    //                        self.ast_ctxt.concat(op3, op1),
    //                        self.ast_ctxt.zx(((op1.getBitvectorSize() + op3.getBitvectorSize()) - op2.getBitvectorSize()), op2)
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "RCL tempory operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);

    //         /* Create the semantics */
    //         let node2 = self.ast_ctxt.extract(dst.get_bit_size()-1, 0, node1);

    //         /* Create symbolic expression */
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst, "RCL operation");

    //         /* Spread taint */
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst, srcCf);

    //         /* Update symbolic flags */
    //         self.cfRcl_s(inst, expr2, node1, op2bis);
    //         self.ofRol_s(inst, expr2, dst, op2bis); /* Same as ROL */
    //         /* Tag undefined flags */
    //         if (op2.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn rcr_s(&mut self, inst: x86Instruction) {
    //         let dst   = inst.operands[0];
    //         let src   = inst.operands[1];
    //         let  srcCf = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1    = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2    = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3    = self.symbolicEngine.getOperandAst(inst, srcCf);

    //         match dst.get_bit_size() {
    //           /* Mask: 0x3f without MOD */
    //           BitSizes::QWORD => {
    //             op2 = self.ast_ctxt.bvand(
    //                     op2,
    //                     self.ast_ctxt.bv(BitSizes::QWORD-1, src.get_bit_size())
    //                   );
    //             }

    //           /* Mask: 0x1f without MOD */
    //           BitSizes::DWORD => {
    //             op2 = self.ast_ctxt.bvand(
    //                     op2,
    //                     self.ast_ctxt.bv(BitSizes::DWORD-1, src.get_bit_size())
    //                   );
    //             }

    //           /* Mask: 0x1f MOD size + 1 */
    //           BitSizes::WORD | BitSizes::BYTE => {
    //             op2 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op2,
    //                       self.ast_ctxt.bv(BitSizes::DWORD-1, src.get_bit_size())),
    //                     self.ast_ctxt.bv(dst.get_bit_size()+1, src.get_bit_size())
    //                   );
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::rcr_s(): Invalid destination size");"#),
    //         }

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvror(
    //                        self.ast_ctxt.concat(op3, op1),
    //                        self.ast_ctxt.zx(((op1.getBitvectorSize() + op3.getBitvectorSize()) - op2.getBitvectorSize()), op2)
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "RCR tempory operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);

    //         /* Create the semantics */
    //         let node2 = self.ast_ctxt.extract(dst.get_bit_size()-1, 0, node1);

    //         /* Create symbolic expression */
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst, "RCR operation");

    //         /* Spread taint */
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst, srcCf);

    //         /* Update symbolic flags */
    //         self.ofRcr_s(inst, expr2, dst, op1, op2); /* OF must be set before CF */
    //         self.cfRcr_s(inst, expr2, dst, node1, op2);

    //         /* Tag undefined flags */
    //         if (op2.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn rdtsc_s(&mut self, inst: x86Instruction) {
    //         let src  = Operand::Register(Register::TSC);
    //         let dst1 = Operand::Register(Register::EDX);
    //         let dst2 = Operand::Register(Register::EAX);

    //         /* Create symbolic operands */
    //         let op   = self.symbolicEngine.getOperandAst(inst, src);
    //         let high = self.ast_ctxt.extract((BitSizes::QWORD - 1), BitSizes::DWORD, op);
    //         let low  = self.ast_ctxt.extract((BitSizes::DWORD - 1), 0, op);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, high, dst1, "RDTSC EDX operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, low, dst2, "RDTSC EAX operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintUnion(dst1, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst2, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn ret_s(&mut self, inst: x86Instruction) {
    //         let stack      = self.architecture.get_stack_pointer();
    //         let stackValue = self.architecture.getConcreteRegisterValue(stack) as u64;
    //         let pc         = Operand::Register(self.architecture.get_program_counter());
    //         let sp         = Operand::Memory(MemoryAccess::new(stackValue, stack.getSize()));

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, sp);

    //         /* Create the semantics */
    //         let node = op1;

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, pc, "Program Counter");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(pc, sp);

    //         /* Create the semantics - side effect */
    //         alignAddStack_s(inst, sp.getSize());

    //         /* Create the semantics - side effect */
    //         if (inst.operands.size() > 0) {
    //           let offset = inst.operands[0].getImmediate();
    //           self.symbolicEngine.getImmediateAst(inst, offset);
    //           alignAddStack_s(inst, offset.getValue() as u32);
    //         }

    //         /* Create the path constraint */
    //         self.symbolicEngine.pushPathConstraint(inst, expr);
    //       }

    //       fn rol_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1    = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2    = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2bis = self.symbolicEngine.getOperandAst(src);

    //         match dst.get_bit_size() {
    //           /* Mask 0x3f MOD size */
    //           BitSizes::QWORD => {
    //             op2 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op2,
    //                       self.ast_ctxt.bv(BitSizes::QWORD-1, src.get_bit_size())),
    //                     self.ast_ctxt.bv(dst.get_bit_size(), src.get_bit_size())
    //                   );

    //             op2bis = self.ast_ctxt.bvand(
    //                        op2bis,
    //                        self.ast_ctxt.bv(BitSizes::QWORD-1, src.get_bit_size())
    //                      );
    //             }

    //           /* Mask 0x1f MOD size */
    //           | BitSizes::DWORD
    //           | BitSizes::WORD
    //           | BitSizes::BYTE => {
    //             op2 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op2,
    //                       self.ast_ctxt.bv(BitSizes::DWORD-1, src.get_bit_size())),
    //                     self.ast_ctxt.bv(dst.get_bit_size(), src.get_bit_size())
    //                   );

    //             op2bis = self.ast_ctxt.bvand(
    //                        op2bis,
    //                        self.ast_ctxt.bv(BitSizes::DWORD-1, src.get_bit_size())
    //                      );
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::rol_s(): Invalid destination size");"#)
    //         }

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvrol(
    //                       op1,
    //                       self.ast_ctxt.zx(op1.getBitvectorSize() - op2.getBitvectorSize(), op2)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ROL operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update symbolic flags */
    //         self.cfRol_s(inst, expr, dst, op2bis);
    //         self.ofRol_s(inst, expr, dst, op2bis);

    //         /* Tag undefined flags */
    //         if (op2.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn ror_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1    = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2    = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2bis = self.symbolicEngine.getOperandAst(src);

    //         match dst.get_bit_size() {
    //           /* Mask 0x3f MOD size */
    //           BitSizes::QWORD => {
    //             op2 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op2,
    //                       self.ast_ctxt.bv(BitSizes::QWORD-1, src.get_bit_size())),
    //                     self.ast_ctxt.bv(dst.get_bit_size(), src.get_bit_size())
    //                   );

    //             op2bis = self.ast_ctxt.bvand(
    //                        op2bis,
    //                        self.ast_ctxt.bv(BitSizes::QWORD-1, src.get_bit_size())
    //                      );
    //             }

    //           /* Mask 0x1f MOD size */
    //           BitSizes::DWORD
    //           |BitSizes::WORD
    //           |BitSizes::BYTE => {
    //             op2 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op2,
    //                       self.ast_ctxt.bv(BitSizes::DWORD-1, src.get_bit_size())),
    //                     self.ast_ctxt.bv(dst.get_bit_size(), src.get_bit_size())
    //                   );

    //             op2bis = self.ast_ctxt.bvand(
    //                        op2bis,
    //                        self.ast_ctxt.bv(BitSizes::DWORD-1, src.get_bit_size())
    //                      );
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::ror_s(): Invalid destination size");"#)
    //         }

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvror(
    //                       op1,
    //                       self.ast_ctxt.zx(op1.getBitvectorSize() - op2.getBitvectorSize(), op2)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "ROR operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update symbolic flags */
    //         self.cfRor_s(inst, expr, dst, op2);
    //         self.ofRor_s(inst, expr, dst, op2bis);

    //         /* Tag undefined flags */
    //         if (op2.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn rorx_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         match dst.get_bit_size() {
    //           /* Mask 0x3f MOD size */
    //           BitSizes::QWORD => {
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::QWORD-1, src2.get_bit_size()));
    //             }

    //           /* Mask 0x1f MOD size */
    //           BitSizes::DWORD => {
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::DWORD-1, src2.get_bit_size()));
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::rorx_s(): Invalid destination size");"#)
    //         }

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvror(
    //                       op1,
    //                       self.ast_ctxt.zx(op1.getBitvectorSize() - op2.getBitvectorSize(), op2)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "RORX operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);
    //         // expr.isTainted |= self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sahf_s(&mut self, inst: x86Instruction) {
    //         let dst1 = Operand::Register(Register::SF);
    //         let dst2 = Operand::Register(Register::ZF);
    //         let dst3 = Operand::Register(Register::AF);
    //         let dst4 = Operand::Register(Register::PF);
    //         let dst5 = Operand::Register(Register::CF);
    //         let src  = Operand::Register(Register::AH);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.extract(7, 7, op1);
    //         let node2 = self.ast_ctxt.extract(6, 6, op1);
    //         let node3 = self.ast_ctxt.extract(4, 4, op1);
    //         let node4 = self.ast_ctxt.extract(2, 2, op1);
    //         let node5 = self.ast_ctxt.extract(0, 0, op1);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst1.getRegister(), "SAHF SF operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, dst2.getRegister(), "SAHF ZF operation");
    //         let expr3 = self.symbolicEngine.createSymbolicExpression(inst, node3, dst3.getRegister(), "SAHF AF operation");
    //         let expr4 = self.symbolicEngine.createSymbolicExpression(inst, node4, dst4.getRegister(), "SAHF PF operation");
    //         let expr5 = self.symbolicEngine.createSymbolicExpression(inst, node5, dst5.getRegister(), "SAHF CF operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst1, src);
    //         // expr2.isTainted = self.taintEngine.taintAssignment(dst2, src);
    //         // expr3.isTainted = self.taintEngine.taintAssignment(dst3, src);
    //         // expr4.isTainted = self.taintEngine.taintAssignment(dst4, src);
    //         // expr5.isTainted = self.taintEngine.taintAssignment(dst5, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sar_s(&mut self, inst: x86Instruction) {
    //         let dst   = inst.operands[0];
    //         let src   = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));

    //         if (dst.get_bit_size() == BitSizes::QWORD){
    //           op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::QWORD-1, dst.get_bit_size()));
    //         }else{
    //           op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::DWORD-1, dst.get_bit_size()));
    // }
    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvashr(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SAR operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update symbolic flags */
    //         self.cfSar_s(inst, expr, dst, op1, op2);
    //         self.ofSar_s(inst, expr, dst, op2);
    //         self.pfShl_s(inst, expr, dst, op2); /* Same that shl */
    //         self.sfShl_s(inst, expr, dst, op2); /* Same that shl */
    //         self.zfShl_s(inst, expr, dst, op2); /* Same that shl */
    //         /* Tag undefined flags */
    //         if (op2.evaluate() != 0) {
    //           self.undefined_s(inst, Register::AF);
    //         }

    //         if (op2.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sarx_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         match dst.get_bit_size() {
    //           /* Mask 0x3f MOD size */
    //           BitSizes::QWORD => {
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::QWORD-1, src2.get_bit_size()));
    //             }

    //           /* Mask 0x1f MOD size */
    //           BitSizes::DWORD => {
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::DWORD-1, src2.get_bit_size()));
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::sarx_s(): Invalid destination size");"#),
    //         }

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvashr(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SARX operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);
    //         // expr.isTainted |= self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sbb_s(&mut self, inst: x86Instruction) {
    //         let dst   = inst.operands[0];
    //         let src   = inst.operands[1];
    //         let  srcCf = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.ast_ctxt.zx(src.get_bit_size()-1, self.symbolicEngine.getOperandAst(inst, srcCf));

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvsub(op1, self.ast_ctxt.bvadd(op2, op3));

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SBB operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, srcCf);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr, dst, op1, op2);
    //         self.cfSub_s(inst, expr, dst, op1, op2);
    //         self.ofSub_s(inst, expr, dst, op1, op2);
    //         self.pf_s(inst, expr, dst);
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn scasb_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* If the REP prefix is defined, convert REP into REPE */
    //         if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP){
    //           inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);}

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvsub(op1, op2);
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::BYTE, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::BYTE, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "SCASB operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.sf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.zf_s(inst, expr1, dst, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn scasd_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* If the REP prefix is defined, convert REP into REPE */
    //         if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP){
    //           inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);}

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvsub(op1, op2);
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::DWORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::DWORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "SCASD operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, dst, op1, op2); //todo: vol = true
    //         self.cfSub_s(inst, expr1, dst, op1, op2); //todo: vol = true
    //         self.ofSub_s(inst, expr1, dst, op1, op2); //todo: vol = true
    //         self.pf_s(inst, expr1, dst); //todo: vol = true
    //         self.sf_s(inst, expr1, dst); //todo: vol = true
    //         self.zf_s(inst, expr1, dst); //todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn scasq_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* If the REP prefix is defined, convert REP into REPE */
    //         if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP){
    //           inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);}

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvsub(op1, op2);
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::QWORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::QWORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "SCASQ operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.sf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.zf_s(inst, expr1, dst, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn scasw_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* If the REP prefix is defined, convert REP into REPE */
    //         if (inst.getPrefix() == triton::arch::x86::ID_PREFIX_REP){
    //           inst.setPrefix(triton::arch::x86::ID_PREFIX_REPE);}

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvsub(op1, op2);
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op4, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op3, self.ast_ctxt.bv(ByteSizes::WORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op3, self.ast_ctxt.bv(ByteSizes::WORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "SCASW operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(dst) | self.taintEngine.isTainted(src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.cfSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.ofSub_s(inst, expr1, dst, op1, op2, ); // todo: vol = true
    //         self.pf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.sf_s(inst, expr1, dst, ); // todo: vol = true
    //         self.zf_s(inst, expr1, dst, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn seta_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  cf  = Operand::Register(Register::CF);
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, cf);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(
    //                         self.ast_ctxt.bvand(
    //                           self.ast_ctxt.bvnot(op2),
    //                           self.ast_ctxt.bvnot(op3)
    //                         ),
    //                         self.ast_ctxt.bvtrue()
    //                       ),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETA operation");

    //         /* Set condition flag */
    //         if (op2.evaluate().is_zero() && op3.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, cf);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setae_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  cf  = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, cf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvfalse()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETAE operation");

    //         /* Set condition flag */
    //         if (op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, cf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  cf  = Operand::Register(Register::CF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, cf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvtrue()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETB operation");

    //         /* Set condition flag */
    //         if (!op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, cf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setbe_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  cf  = Operand::Register(Register::CF);
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, cf);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(self.ast_ctxt.bvor(op2, op3), self.ast_ctxt.bvtrue()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETBE operation");

    //         /* Set condition flag */
    //         if (!op2.evaluate().is_zero() || !op3.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, cf);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sete_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvtrue()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETE operation");

    //         /* Set condition flag */
    //         if (!op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setg_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  sf  = Operand::Register(Register::SF);
    //         let  of  = Operand::Register(Register::OF);
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(self.ast_ctxt.bvor(self.ast_ctxt.bvxor(op2, op3), op4), self.ast_ctxt.bvfalse()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETG operation");

    //         /* Set condition flag */
    //         if ((op2.evaluate().is_zero() == op3.evaluate().is_zero()) && op4.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, sf);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, of);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setge_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  sf  = Operand::Register(Register::SF);
    //         let  of  = Operand::Register(Register::OF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, of);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, op3),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETGE operation");

    //         /* Set condition flag */
    //         if (op2.evaluate().is_zero() == op3.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, sf);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, of);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setl_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  sf  = Operand::Register(Register::SF);
    //         let  of  = Operand::Register(Register::OF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, of);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(self.ast_ctxt.bvxor(op2, op3), self.ast_ctxt.bvtrue()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETL operation");

    //         /* Set condition flag */
    //         if (op2.evaluate().is_zero() != op3.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, sf);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, of);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setle_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  sf  = Operand::Register(Register::SF);
    //         let  of  = Operand::Register(Register::OF);
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, sf);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, of);
    //         let op4 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(self.ast_ctxt.bvor(self.ast_ctxt.bvxor(op2, op3), op4), self.ast_ctxt.bvtrue()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETLE operation");

    //         /* Set condition flag */
    //         if ((op2.evaluate().is_zero() != op3.evaluate().is_zero()) || !op4.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, sf);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, of);
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setne_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  zf  = Operand::Register(Register::ZF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, zf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvfalse()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETNE operation");

    //         /* Set condition flag */
    //         if (op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, zf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setno_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  of  = Operand::Register(Register::OF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, of);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvfalse()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETNO operation");

    //         /* Set condition flag */
    //         if (op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, of);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setnp_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  pf  = Operand::Register(Register::PF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, pf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvfalse()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETNP operation");

    //         /* Set condition flag */
    //         if (op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, pf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setns_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  sf  = Operand::Register(Register::SF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, sf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvfalse()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETNS operation");

    //         /* Set condition flag */
    //         if (op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, sf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn seto_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  of  = Operand::Register(Register::OF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, of);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvtrue()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETO operation");

    //         /* Set condition flag */
    //         if (!op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, of);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn setp_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  pf  = Operand::Register(Register::PF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, pf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvtrue()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETP operation");

    //         /* Set condition flag */
    //         if (!op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, pf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sets_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  sf  = Operand::Register(Register::SF);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, sf);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.ite(
    //                       self.ast_ctxt.equal(op2, self.ast_ctxt.bvtrue()),
    //                       self.ast_ctxt.bv(1, dst.get_bit_size()),
    //                       self.ast_ctxt.bv(0, dst.get_bit_size())
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SETS operation");

    //         /* Set condition flag */
    //         if (!op2.evaluate().is_zero()) {
    //           inst.setConditionTaken(true);
    //         }

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, sf);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sfence_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn shl_s(&mut self, inst: x86Instruction) {
    //         let dst   = inst.operands[0];
    //         let src   = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1    = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2    = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));
    //         let op2bis = op2;

    //         if (dst.get_bit_size() == BitSizes::QWORD){
    //           op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::QWORD-1, dst.get_bit_size()));
    //         }else{
    //           op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::DWORD-1, dst.get_bit_size()));
    // }
    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvshl(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SHL operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update symbolic flags */
    //         self.cfShl_s(inst, expr, dst, op1, op2);
    //         self.ofShl_s(inst, expr, dst, op1, op2);
    //         self.pfShl_s(inst, expr, dst, op2);
    //         self.sfShl_s(inst, expr, dst, op2);
    //         self.zfShl_s(inst, expr, dst, op2);

    //         /* Tag undefined flags */
    //         if (op2.evaluate() != 0) {
    //           self.undefined_s(inst, Register::AF);
    //         }

    //         if (op2bis.evaluate() > dst.get_bit_size()) {
    //           self.undefined_s(inst, Register::CF);
    //         }

    //         if (op2.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn shld_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1    = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2    = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3    = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3bis = op3;

    //         match dst.get_bit_size() {
    //           /* Mask 0x3f MOD size */
    //           BitSizes::QWORD => {
    //             op3 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op3,
    //                       self.ast_ctxt.bv(BitSizes::QWORD-1, src2.get_bit_size())),
    //                     self.ast_ctxt.bv(dst.get_bit_size(), src2.get_bit_size())
    //                   );
    //             }

    //           /* Mask 0x1f MOD size */
    //           BitSizes::DWORD | BitSizes::WORD => {
    //             op3 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op3,
    //                       self.ast_ctxt.bv(BitSizes::DWORD-1, src2.get_bit_size())),
    //                     self.ast_ctxt.bv(BitSizes::DWORD, src2.get_bit_size())
    //                   );
    //             }

    //           _ =>
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::shld_s(): Invalid destination size");"#),
    //         }

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.extract(
    //                       dst.get_bit_size()-1, 0,
    //                       self.ast_ctxt.bvrol(
    //                         self.ast_ctxt.concat(op2, op1),
    //                         self.ast_ctxt.zx(((op1.getBitvectorSize() + op2.getBitvectorSize()) - op3.getBitvectorSize()), op3)
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SHLD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);
    //         // expr.isTainted |= self.taintEngine.taintUnion(dst, src2);

    //         /* Update symbolic flags */
    //         self.cfShld_s(inst, expr, dst, op1, op2, op3);
    //         self.ofShld_s(inst, expr, dst, op1, op2, op3);
    //         self.pfShl_s(inst, expr, dst, op3); /* Same that shl */
    //         self.sfShld_s(inst, expr, dst, op1, op2, op3);
    //         self.zfShl_s(inst, expr, dst, op3); /* Same that shl */
    //         /* Tag undefined flags */
    //         if (op3.evaluate() != 0) {
    //           self.undefined_s(inst, Register::AF);
    //         }

    //         if (op3.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         if (op3bis.evaluate() > dst.get_bit_size()) {
    //           self.undefined_s(inst, Register::AF);
    //           self.undefined_s(inst, Register::CF);
    //           self.undefined_s(inst, Register::OF);
    //           self.undefined_s(inst, Register::PF);
    //           self.undefined_s(inst, Register::SF);
    //           self.undefined_s(inst, Register::ZF);
    //           if (dst.getType() == triton::arch::OP_REG){
    //             self.undefined_s(inst, dst.getRegister());}
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn shlx_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         match dst.get_bit_size() {
    //           /* Mask 0x3f MOD size */
    //           BitSizes::QWORD => {
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::QWORD-1, src2.get_bit_size()));
    //             }

    //           /* Mask 0x1f MOD size */
    //           BitSizes::DWORD => {
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::DWORD-1, src2.get_bit_size()));
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::shlx_s(): Invalid destination size");"#)
    //         }

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvshl(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SHLX operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);
    //         // expr.isTainted |= self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn shr_s(&mut self, inst: x86Instruction) {
    //         let dst   = inst.operands[0];
    //         let src   = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1    = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2    = self.ast_ctxt.zx(dst.get_bit_size() - src.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src));
    //         let op2bis = op2;

    //         if (dst.get_bit_size() == BitSizes::QWORD){
    //           op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::QWORD-1, dst.get_bit_size()));
    //         }else{
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::DWORD-1, dst.get_bit_size()));
    // }
    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvlshr(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SHR operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update symbolic flags */
    //         self.cfShr_s(inst, expr, dst, op1, op2);
    //         self.ofShr_s(inst, expr, dst, op1, op2);
    //         self.pfShl_s(inst, expr, dst, op2); /* Same that shl */
    //         self.sfShl_s(inst, expr, dst, op2); /* Same that shl */
    //         self.zfShl_s(inst, expr, dst, op2); /* Same that shl */
    //         /* Tag undefined flags */
    //         if (op2.evaluate() != 0) {
    //           self.undefined_s(inst, Register::AF);
    //         }

    //         if (op2bis.evaluate() > dst.get_bit_size()) {
    //           self.undefined_s(inst, Register::CF);
    //         }

    //         if (op2.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn shrd_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1    = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2    = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3    = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3bis = op3;

    //         match dst.get_bit_size() {
    //           /* Mask 0x3f MOD size */
    //           BitSizes::QWORD => {
    //             op3 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op3,
    //                       self.ast_ctxt.bv(BitSizes::QWORD-1, src2.get_bit_size())),
    //                     self.ast_ctxt.bv(dst.get_bit_size(), src2.get_bit_size())
    //                   );
    //             }

    //           /* Mask 0x1f MOD size */
    //           BitSizes::DWORD | BitSizes::WORD => {
    //             op3 = self.ast_ctxt.bvsmod(
    //                     self.ast_ctxt.bvand(
    //                       op3,
    //                       self.ast_ctxt.bv(BitSizes::DWORD-1, src2.get_bit_size())),
    //                     self.ast_ctxt.bv(BitSizes::DWORD, src2.get_bit_size())
    //                   );
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::shrd_s(): Invalid destination size");"#)
    //         }

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.extract(
    //                       dst.get_bit_size()-1, 0,
    //                       self.ast_ctxt.bvror(
    //                         self.ast_ctxt.concat(op2, op1),
    //                         self.ast_ctxt.zx(((op1.getBitvectorSize() + op2.getBitvectorSize()) - op3.getBitvectorSize()), op3)
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SHRD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);
    //         // expr.isTainted |= self.taintEngine.taintUnion(dst, src2);

    //         /* Update symbolic flags */
    //         self.cfShrd_s(inst, expr, dst, op1, op2, op3);
    //         self.ofShrd_s(inst, expr, dst, op1, op2, op3);
    //         self.pfShl_s(inst, expr, dst, op3); /* Same that shl */
    //         self.sfShrd_s(inst, expr, dst, op1, op2, op3);
    //         self.zfShl_s(inst, expr, dst, op3); /* Same that shl */
    //         /* Tag undefined flags */
    //         if (op3.evaluate() != 0) {
    //           self.undefined_s(inst, Register::AF);
    //         }

    //         if (op3.evaluate() > 1) {
    //           self.undefined_s(inst, Register::OF);
    //         }

    //         if (op3bis.evaluate() > dst.get_bit_size()) {
    //           self.undefined_s(inst, Register::AF);
    //           self.undefined_s(inst, Register::CF);
    //           self.undefined_s(inst, Register::OF);
    //           self.undefined_s(inst, Register::PF);
    //           self.undefined_s(inst, Register::SF);
    //           self.undefined_s(inst, Register::ZF);
    //           if (dst.getType() == triton::arch::OP_REG){
    //             self.undefined_s(inst, dst.getRegister());}
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn shrx_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         match dst.get_bit_size() {
    //           /* Mask 0x3f MOD size */
    //           BitSizes::QWORD => {
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::QWORD-1, src2.get_bit_size()));
    //             }

    //           /* Mask 0x1f MOD size */
    //           BitSizes::DWORD => {
    //             op2 = self.ast_ctxt.bvand(op2, self.ast_ctxt.bv(BitSizes::DWORD-1, src2.get_bit_size()));
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::shrx_s(): Invalid destination size");"#)
    //         }

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvlshr(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SHRX operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);
    //         // expr.isTainted |= self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn stc_s(&mut self, inst: x86Instruction) {
    //         self.setFlag_s(inst, Register::CF, "Sets carry flag");
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn std_s(&mut self, inst: x86Instruction) {
    //         self.setFlag_s(inst, Register::DF, "Sets direction flag");
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sti_s(&mut self, inst: x86Instruction) {
    //         self.setFlag_s(inst, Register::IF, "Sets interrupt flag");
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn stmxcsr_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let  src = Operand::Register(Register::MXCSR);

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "STMXCSR operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn stosb_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::BYTE, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::BYTE, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "STOSB operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn stosd_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::DWORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::DWORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "STOSD operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn stosq_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::QWORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::QWORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "STOSQ operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn stosw_s(&mut self, inst: x86Instruction) {
    //         let dst    = inst.operands[0];
    //         let src    = inst.operands[1];
    //         let  index  = Operand::Register(Register::DI.full_register());
    //         let  cx     = Operand::Register(Register::CX.full_register());
    //         let  df     = Operand::Register(Register::DF);

    //         /* Check if there is a REP prefix and a counter to zero */
    //         if (inst.getPrefix() != triton::arch::x86::ID_PREFIX_INVALID && self.symbolicEngine.getOperandAst(cx).evaluate().is_zero()) {
    //           self.controlFlow_s(inst);
    //           return;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, index);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, df);

    //         /* Create the semantics */
    //         let node1 = op1;
    //         let node2 = self.ast_ctxt.ite(
    //                        self.ast_ctxt.equal(op3, self.ast_ctxt.bvfalse()),
    //                        self.ast_ctxt.bvadd(op2, self.ast_ctxt.bv(ByteSizes::WORD, index.get_bit_size())),
    //                        self.ast_ctxt.bvsub(op2, self.ast_ctxt.bv(ByteSizes::WORD, index.get_bit_size()))
    //                      );

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "STOSW operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, index, "Index operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         // expr2.isTainted = self.taintEngine.taintUnion(index, index);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    fn sub_s(&mut self, inst: x86Instruction) {
        let dst = OperandWrapper(inst, 0);
        let src = OperandWrapper(inst, 1);
        // let dst = inst.operands[0];
        // let src = inst.operands[1];

        /* Create symbolic operands */
        let op1 = AstBuilder::get_operand_ast(inst, 0);
        let op2 = AstBuilder::get_operand_ast(inst, 1);
        // let op1 = self.symbolicEngine.getOperandAst(inst, dst);
        // let op2 = self.symbolicEngine.getOperandAst(inst, src);

        /* Create the semantics */
        let node = self.ast_ctxt.bvsub(op1, op2);

        // /* Create symbolic expression */
        // let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "SUB operation");

        // /* Spread taint */
        // // expr.isTainted = self.taintEngine.taintUnion(dst, src);

        // /* Update symbolic flags */
        self.af_s(inst, node, dst, op1, op2);
        self.cfSub_s(inst, node, dst, op1, op2);
        self.ofSub_s(inst, node, dst, op1, op2);
        self.pf_s(inst, node, dst);
        self.sf_s(inst, node, dst);
        self.zf_s(inst, node, dst);

        // /* Update the symbolic control flow */
        // self.controlFlow_s(inst);
    }

    //       fn syscall_s(&mut self, inst: x86Instruction) {
    //         let dst1 = Operand::Register(Register::CX.full_register());
    //         let src1 = Operand::Register(self.architecture.get_program_counter());

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvadd(op1, self.ast_ctxt.bv(inst.getSize(), src1.get_bit_size()));

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst1, "SYSCALL RCX operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.taintAssignment(dst1, src1);

    //         /* 64-bit */
    //         if (src1.get_bit_size() == 64) {
    //           let dst2 = Operand::Register(Register::R11);
    //           let src2 = Operand::Register(Register::EFLAGS);
    //           /* Create symbolic operands */
    //           let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //           /* Create symbolic expression */
    //           let expr2 = self.symbolicEngine.createSymbolicExpression(inst, op2, dst2, "SYSCALL R11 operation");
    //           /* Spread taint */
    //         //   expr2.isTainted = self.taintEngine.taintAssignment(dst2, src2);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn sysenter_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn test_s(&mut self, inst: x86Instruction) {
    //         let src1 = inst.operands[0];
    //         let src2 = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicVolatileExpression(inst, node, "TEST operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2);

    //         /* Update symbolic flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.clearFlag_s(inst, Register::CF, "Clears carry flag");
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.pf_s(inst, expr, src1, ); // todo: vol = true
    //         self.sf_s(inst, expr, src1, ); // todo: vol = true
    //         self.zf_s(inst, expr, src1, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn tzcnt_s(&mut self, inst: x86Instruction) {
    //         let dst     = inst.operands[0];
    //         let src     = inst.operands[1];
    //         let  bvSize1 = dst.get_bit_size();
    //         let  bvSize2 = src.get_bit_size();

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut node: Instruction;
    //         match src.getSize() {
    //           ByteSizes::BYTE => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, bvSize2)),
    //                      self.ast_ctxt.bv(bvSize1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))
    //                    );
    //                 }
    //           ByteSizes::WORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, bvSize2)),
    //                      self.ast_ctxt.bv(bvSize1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))
    //                    );
    //                 }
    //           ByteSizes::DWORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, bvSize2)),
    //                      self.ast_ctxt.bv(bvSize1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(16, 16, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(16, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(17, 17, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(17, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(18, 18, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(18, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(19, 19, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(19, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(20, 20, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(20, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(21, 21, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(21, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(22, 22, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(22, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(23, 23, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(23, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(24, 24, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(24, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(25, 25, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(25, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(26, 26, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(26, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(27, 27, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(27, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(28, 28, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(28, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(29, 29, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(29, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(30, 30, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(30, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(31, 31, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(31, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))))))))))))))))))
    //                    );
    //                 }
    //           ByteSizes::QWORD => {
    //             node = self.ast_ctxt.ite(
    //                      self.ast_ctxt.equal(op1, self.ast_ctxt.bv(0, bvSize2)),
    //                      self.ast_ctxt.bv(bvSize1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(0, 0, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(0, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(1, 1, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(1, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(2, 2, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(2, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(3, 3, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(3, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(4, 4, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(4, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(5, 5, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(5, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(6, 6, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(6, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(7, 7, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(7, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(8, 8, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(8, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(9, 9, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(9, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(10, 10, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(10, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(11, 11, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(11, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(12, 12, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(12, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(13, 13, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(13, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(14, 14, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(14, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(15, 15, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(15, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(16, 16, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(16, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(17, 17, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(17, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(18, 18, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(18, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(19, 19, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(19, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(20, 20, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(20, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(21, 21, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(21, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(22, 22, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(22, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(23, 23, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(23, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(24, 24, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(24, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(25, 25, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(25, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(26, 26, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(26, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(27, 27, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(27, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(28, 28, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(28, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(29, 29, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(29, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(30, 30, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(30, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(31, 31, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(31, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(32, 32, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(32, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(33, 33, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(33, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(34, 34, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(34, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(35, 35, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(35, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(36, 36, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(36, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(37, 37, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(37, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(38, 38, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(38, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(39, 39, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(39, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(40, 40, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(40, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(41, 41, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(41, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(42, 42, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(42, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(43, 43, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(43, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(44, 44, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(44, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(45, 45, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(45, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(46, 46, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(46, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(47, 47, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(47, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(48, 48, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(48, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(49, 49, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(49, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(50, 50, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(50, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(51, 51, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(51, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(52, 52, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(52, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(53, 53, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(53, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(54, 54, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(54, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(55, 55, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(55, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(56, 56, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(56, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(57, 57, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(57, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(58, 58, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(58, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(59, 59, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(59, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(60, 60, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(60, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(61, 61, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(61, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(62, 62, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(62, bvSize1),
    //                      self.ast_ctxt.ite(self.ast_ctxt.equal(self.ast_ctxt.extract(63, 63, op1), self.ast_ctxt.bvtrue()), self.ast_ctxt.bv(63, bvSize1),
    //                      self.ast_ctxt.bv(0, bvSize1)
    //                      ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    //                    );
    //                 }
    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::tzcnt_s(): Invalid operand size.");"#)
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "TZCNT operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update symbolic flags */
    //         self.cfTzcnt_s(inst, expr, src, op1);
    //         self.zf_s(inst, expr, src);

    //         /* Tag undefined flags */
    //         self.undefined_s(inst, Register::OF);
    //         self.undefined_s(inst, Register::SF);
    //         self.undefined_s(inst, Register::PF);
    //         self.undefined_s(inst, Register::AF);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn unpckhpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.concat(
    //                       self.ast_ctxt.extract(127, 64, op2),
    //                       self.ast_ctxt.extract(127, 64, op1)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "UNPCKHPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn unpckhps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(4);

    //         unpack.push(self.ast_ctxt.extract(127, 96, op2));
    //         unpack.push(self.ast_ctxt.extract(127, 96, op1));
    //         unpack.push(self.ast_ctxt.extract(95, 64, op2));
    //         unpack.push(self.ast_ctxt.extract(95, 64, op1));

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "UNPCKHPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn unpcklpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.concat(
    //                       self.ast_ctxt.extract(63, 0, op2),
    //                       self.ast_ctxt.extract(63, 0, op1)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "UNPCKLPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn unpcklps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(4);

    //         unpack.push(self.ast_ctxt.extract(63, 32, op2));
    //         unpack.push(self.ast_ctxt.extract(63, 32, op1));
    //         unpack.push(self.ast_ctxt.extract(31, 0, op2));
    //         unpack.push(self.ast_ctxt.extract(31, 0, op1));

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "UNPCKLPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vextracti128_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut node: Instruction;
    //         if (op2.evaluate() & 0b00000001) {
    //           node = self.ast_ctxt.extract(255, 128, op1);
    //         } else {
    //           node = self.ast_ctxt.extract(127, 0, op1);
    //         }

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VEXTRACTI128 operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vmovd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.extract(BitSizes::DWORD-1, 0, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vmovdqa_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVDQA operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vmovdqu_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVDQU operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vmovntdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVNTDQ operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vmovq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.extract(BitSizes::QWORD-1, 0, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVQ operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vmovsd_s(&mut self, inst: x86Instruction) {
    //         /* Move scalar double-precision floating-point value */
    //         if (inst.operands.size() == 2) {
    //           let dst = inst.operands[0];
    //           let src = inst.operands[1];

    //           /* Create symbolic operands */
    //           let op1  = self.symbolicEngine.getOperandAst(inst, dst);
    //           let op2  = self.symbolicEngine.getOperandAst(inst, src);

    //           /* Create the semantics */
    //           let mut node: Instruction;
    //           if (dst.getSize() == ByteSizes::DQWORD && src.getSize() == ByteSizes::QWORD) {
    //             /* VEX.LIG.F2.0F.WIG 10 /r VMOVSD xmm1, m64 */
    //             node = op2;
    //           }
    //           else if (dst.getSize() == ByteSizes::QWORD && src.getSize() == ByteSizes::DQWORD) {
    //             /* VEX.LIG.F2.0F.WIG 11 /r VMOVSD m64, xmm1 */
    //             node = self.ast_ctxt.extract(BitSizes::QWORD - 1, 0, op2);
    //           }
    //           else {
    //             todo!(r#"triton::exceptions::Semantics("x86Semantics::vmovsd_s(): Invalid operand size.");"#);
    //           }

    //           /* Create symbolic expression */
    //           let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVSD operation");

    //           /* Spread taint */
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, src);
    //         }

    //         /* Merge scalar double-precision floating-point value
    //          *
    //          * VEX.NDS.LIG.F2.0F.WIG 10 /r VMOVSD xmm1, xmm2, xmm3
    //          * VEX.NDS.LIG.F2.0F.WIG 11 /r VMOVSD xmm1, xmm2, xmm3
    //          */
    //         else if (inst.operands.size() == 3) {
    //           let dst = inst.operands[0];
    //           let src1 = inst.operands[1];
    //           let src2 = inst.operands[2];

    //            /* Create symbolic operands */
    //           let op1  = self.symbolicEngine.getOperandAst(inst, dst);
    //           let op2  = self.symbolicEngine.getOperandAst(inst, src1);
    //           let op3  = self.symbolicEngine.getOperandAst(inst, src2);

    //           /* Create the semantics */
    //           let node = self.ast_ctxt.concat(
    //                         self.ast_ctxt.extract(BitSizes::DQWORD - 1, BitSizes::QWORD, op2),
    //                         self.ast_ctxt.extract(BitSizes::QWORD - 1, 0, op3)
    //                       );

    //           /* Create symbolic expression */
    //           let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVSD operation");

    //           /* Spread taint */
    //         // //   expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vmovaps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVAPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vmovups_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create the semantics */
    //         let node = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VMOVUPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpackuswb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         std::vector<triton::ast::SharedAbstractNode> ops{op2, op1};
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           for idx in 0..(ops.size()) {
    //             for (let mut i: u32 = ByteSizes::QWORD * k; i < ByteSizes::QWORD * (k + 1); ++i) {
    //               let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //               let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //               let signed_word = self.ast_ctxt.extract(high, low, ops[idx]);
    //               pck.push(self.ast_ctxt.ite(
    //                       self.ast_ctxt.bvsge(signed_word, self.ast_ctxt.bv(0xff, BitSizes::WORD)),
    //                       self.ast_ctxt.bv(0xff, BitSizes::BYTE),
    //                       self.ast_ctxt.ite(
    //                               self.ast_ctxt.bvsle(signed_word, self.ast_ctxt.bv(0x00, BitSizes::WORD)),
    //                               self.ast_ctxt.bv(0x00, BitSizes::BYTE),
    //                               self.ast_ctxt.extract(BitSizes::BYTE - 1, 0, signed_word)))
    //               );
    //             }
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPACKUSWB operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpackssdw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         std::vector<triton::ast::SharedAbstractNode> ops{op2, op1};
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           for idx in 0..(ops.size()) {
    //             for (let mut i: u32 = ByteSizes::DWORD * k; i < ByteSizes::DWORD * (k + 1); ++i) {
    //               let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::DWORD);
    //               let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (i * BitSizes::DWORD);
    //               let signed_dword = self.ast_ctxt.extract(high, low, ops[idx]);
    //               pck.push(self.ast_ctxt.ite(
    //                       self.ast_ctxt.bvsge(signed_dword, self.ast_ctxt.bv(0x7fff, BitSizes::DWORD)),
    //                       self.ast_ctxt.bv(0x7fff, BitSizes::WORD),
    //                       self.ast_ctxt.ite(
    //                               self.ast_ctxt.bvsle(signed_dword, self.ast_ctxt.bv(0xffff8000, BitSizes::DWORD)),
    //                               self.ast_ctxt.bv(0x8000, BitSizes::WORD),
    //                               self.ast_ctxt.extract(BitSizes::WORD - 1, 0, signed_dword)))
    //               );
    //             }
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPACKSSDW operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpacksswb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         std::vector<triton::ast::SharedAbstractNode> ops{op2, op1};
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           for idx in 0..(ops.size()) {
    //             for (let mut i: u32 = ByteSizes::QWORD * k; i < ByteSizes::QWORD * (k + 1); ++i) {
    //               let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //               let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //               let signed_word = self.ast_ctxt.extract(high, low, ops[idx]);
    //               pck.push(self.ast_ctxt.ite(
    //                       self.ast_ctxt.bvsge(signed_word, self.ast_ctxt.bv(0x007f, BitSizes::WORD)),
    //                       self.ast_ctxt.bv(0x7f, BitSizes::BYTE),
    //                       self.ast_ctxt.ite(
    //                               self.ast_ctxt.bvsle(signed_word, self.ast_ctxt.bv(0xff80, BitSizes::WORD)),
    //                               self.ast_ctxt.bv(0x80, BitSizes::BYTE),
    //                               self.ast_ctxt.extract(BitSizes::BYTE - 1, 0, signed_word)))
    //               );
    //             }
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPACKSSWB operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpaddb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::BYTE);

    //         for i in 0..(dst.getSize() / ByteSizes::BYTE) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (i * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(high, low, op1), self.ast_ctxt.extract(high, low, op2)));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPADDB operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpaddd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         for i in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (i * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(high, low, op1), self.ast_ctxt.extract(high, low, op2)));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPADDD operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpaddw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.bvadd(self.ast_ctxt.extract(high, low, op1), self.ast_ctxt.extract(high, low, op2)));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPADDW operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpand_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(op2, op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPAND operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpandn_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvand(self.ast_ctxt.bvnot(op2), op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPANDN operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vperm2i128_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];
    //         let src3 = inst.operands[3];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src3);

    //         /* Create the semantics */
    //         std::deque<triton::arch::OperandWrapper> taint;
    //         let permute = [&] (triton::uint8 control) {
    //           switch (control) {
    //             case 0:
    //               taint.push(src1);
    //               return self.ast_ctxt.extract(127, 0, op1);
    //             case 1:
    //               taint.push(src1);
    //               return self.ast_ctxt.extract(255, 128, op1);
    //             case 2:
    //               taint.push(src2);
    //               return self.ast_ctxt.extract(127, 0, op2);
    //             case 3:
    //             default:
    //               taint.push(src2);
    //               return self.ast_ctxt.extract(255, 128, op2);
    //           }
    //         };

    //         let ctrl = static_cast<triton::uint8>(op3.evaluate());
    //         let high = permute((ctrl >> 4) & 0b00000011);
    //         let low = permute(ctrl & 0b00000011);

    //         if (ctrl & 0b00001000) {
    //           low = self.ast_ctxt.bv(0, 128);
    //           taint.pop_back();
    //         }

    //         if (ctrl & 0b10000000) {
    //           high = self.ast_ctxt.bv(0, 128);
    //           taint.pop_front();
    //         }

    //         let node = self.ast_ctxt.concat(high, low);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPERM2I128 operation");

    //         /* Spread taint */
    //         if (taint.empty()) {
    //         //   self.taintEngine.setTaint(dst, false);
    //         } else if (taint.size() == 1) {
    //         //   expr.isTainted = self.taintEngine.taintAssignment(dst, taint[0]);
    //         } else {
    //         // //   expr.isTainted = self.taintEngine.taintAssignment(dst, taint[0]) | self.taintEngine.taintUnion(dst, taint[0]);
    //         }

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpermq_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::BYTE);

    //         for i in 0..(dst.getSize() / ByteSizes::QWORD) {
    //           let high = BitSizes::BYTE - 1 - 2 * i;
    //           let shift = self.ast_ctxt.bvmul(
    //                          self.ast_ctxt.bv(BitSizes::QWORD, src1.get_bit_size()),
    //                          self.ast_ctxt.zx(src1.get_bit_size() - 2,
    //                            self.ast_ctxt.extract(high, high - 1, op2)));
    //           pck.push(self.ast_ctxt.extract(BitSizes::QWORD - 1, 0, self.ast_ctxt.bvlshr(op1, shift)));
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPERMQ operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpextrb_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         let node = self.ast_ctxt.extract(7, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bv(((op3.evaluate() & 0x0f) * 8), op2.getBitvectorSize())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPEXTRB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpextrd_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         let node = self.ast_ctxt.extract(BitSizes::DWORD - 1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bv(((op3.evaluate() & 0x3) * BitSizes::DWORD), op2.getBitvectorSize())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPEXTRD operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpextrq_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         let node = self.ast_ctxt.extract(BitSizes::QWORD - 1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bv(((op3.evaluate() & 0x1) * BitSizes::QWORD), op2.getBitvectorSize())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPEXTRQ operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpextrw_s(&mut self, inst: x86Instruction) {
    //         let mut count: u32 = 0;
    //         let dst            = inst.operands[0];
    //         let src1           = inst.operands[1];
    //         let src2           = inst.operands[2];

    //         /*
    //          * When specifying a word location in an MMX technology register, the
    //          * 2 least-significant bits of the count operand specify the location;
    //          * for an XMM register, the 3 least-significant bits specify the
    //          * location.
    //          */
    //         if (src1.get_bit_size() == BitSizes::QWORD) {
    //           count = 0x03;
    //         }
    //         else {
    //           count = 0x07;
    //         }

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         let node = self.ast_ctxt.extract(BitSizes::WORD - 1, 0,
    //                       self.ast_ctxt.bvlshr(
    //                         op2,
    //                         self.ast_ctxt.bv(((op3.evaluate() & count) * BitSizes::WORD), op2.getBitvectorSize())
    //                       )
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPEXTRW operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src1);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpbroadcastb_s(&mut self, inst: x86Instruction) {
    //         let &dst = inst.operands[0];
    //         let &src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let src_node = self.ast_ctxt.extract(BitSizes::BYTE - 1, 0, op);
    //         std::vector<triton::ast::SharedAbstractNode> exprs(dst.getSize(), src_node);
    //         let node = self.ast_ctxt.concat(exprs);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPBROADCASTB operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpcmpeqb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(src1.getSize()) {
    //           let high: u32 = (src1.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (src1.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.equal(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xff, BitSizes::BYTE),
    //                           self.ast_ctxt.bv(0x00, BitSizes::BYTE))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPCMPEQB operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpcmpeqd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.equal(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffffffff, BitSizes::DWORD),
    //                           self.ast_ctxt.bv(0x00000000, BitSizes::DWORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPCMPEQD operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpcmpeqq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::QWORD);

    //         for index in 0..(dst.getSize() / ByteSizes::QWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::QWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::QWORD) - (index * BitSizes::QWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.equal(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffffffffffffffff, BitSizes::QWORD),
    //                           self.ast_ctxt.bv(0x0000000000000000, BitSizes::QWORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPCMPEQQ operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpcmpeqw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.equal(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffff, BitSizes::WORD),
    //                           self.ast_ctxt.bv(0x0000, BitSizes::WORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPCMPEQW operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpcmpgtb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsgt(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xff, BitSizes::BYTE),
    //                           self.ast_ctxt.bv(0x00, BitSizes::BYTE))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPCMPGTB operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpcmpgtd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsgt(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffffffff, BitSizes::DWORD),
    //                           self.ast_ctxt.bv(0x00000000, BitSizes::DWORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPCMPGTD operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpcmpgtw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsgt(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.bv(0xffff, BitSizes::WORD),
    //                           self.ast_ctxt.bv(0x0000, BitSizes::WORD))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPCMPGTW operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpmaddwd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         for (let mut i: u32 = 0; i < dst.getSize() / ByteSizes::WORD; i += 2) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           let node1 = self.ast_ctxt.bvmul(
    //                          self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op1)),
    //                          self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op2))
    //                        );
    //           high -= BitSizes::WORD;
    //           low  -= BitSizes::WORD;
    //           let node2 = self.ast_ctxt.bvmul(
    //                          self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op1)),
    //                          self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op2))
    //                        );
    //           pck.push(self.ast_ctxt.bvadd(node1, node2));
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPMADDWD operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpmovmskb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let mut mskb: Vec<Instruction> = Vec::new();
    //         mskb.reserve(32);

    //         match src.getSize() {
    //           ByteSizes::QQWORD => {
    //             mskb.push(self.ast_ctxt.extract(255, 255, op2));
    //             mskb.push(self.ast_ctxt.extract(247, 247, op2));
    //             mskb.push(self.ast_ctxt.extract(239, 239, op2));
    //             mskb.push(self.ast_ctxt.extract(231, 231, op2));
    //             mskb.push(self.ast_ctxt.extract(223, 223, op2));
    //             mskb.push(self.ast_ctxt.extract(215, 215, op2));
    //             mskb.push(self.ast_ctxt.extract(207, 207, op2));
    //             mskb.push(self.ast_ctxt.extract(199, 199, op2));
    //             mskb.push(self.ast_ctxt.extract(191, 191, op2));
    //             mskb.push(self.ast_ctxt.extract(183, 183, op2));
    //             mskb.push(self.ast_ctxt.extract(175, 175, op2));
    //             mskb.push(self.ast_ctxt.extract(167, 167, op2));
    //             mskb.push(self.ast_ctxt.extract(159, 159, op2));
    //             mskb.push(self.ast_ctxt.extract(151, 151, op2));
    //             mskb.push(self.ast_ctxt.extract(143, 143, op2));
    //             mskb.push(self.ast_ctxt.extract(135, 135, op2));

    //             // todo: duplicated below
    //             mskb.push(self.ast_ctxt.extract(127, 127, op2));
    //             mskb.push(self.ast_ctxt.extract(119, 119, op2));
    //             mskb.push(self.ast_ctxt.extract(111, 111, op2));
    //             mskb.push(self.ast_ctxt.extract(103, 103, op2));
    //             mskb.push(self.ast_ctxt.extract(95 , 95 , op2));
    //             mskb.push(self.ast_ctxt.extract(87 , 87 , op2));
    //             mskb.push(self.ast_ctxt.extract(79 , 79 , op2));
    //             mskb.push(self.ast_ctxt.extract(71 , 71 , op2));
    //             mskb.push(self.ast_ctxt.extract(63 , 63 , op2));
    //             mskb.push(self.ast_ctxt.extract(55 , 55 , op2));
    //             mskb.push(self.ast_ctxt.extract(47 , 47 , op2));
    //             mskb.push(self.ast_ctxt.extract(39 , 39 , op2));
    //             mskb.push(self.ast_ctxt.extract(31 , 31 , op2));
    //             mskb.push(self.ast_ctxt.extract(23 , 23 , op2));
    //             mskb.push(self.ast_ctxt.extract(15 , 15 , op2));
    //             mskb.push(self.ast_ctxt.extract(7  , 7  , op2));
    //           }

    //           ByteSizes::DQWORD => {
    //             mskb.push(self.ast_ctxt.extract(127, 127, op2));
    //             mskb.push(self.ast_ctxt.extract(119, 119, op2));
    //             mskb.push(self.ast_ctxt.extract(111, 111, op2));
    //             mskb.push(self.ast_ctxt.extract(103, 103, op2));
    //             mskb.push(self.ast_ctxt.extract(95 , 95 , op2));
    //             mskb.push(self.ast_ctxt.extract(87 , 87 , op2));
    //             mskb.push(self.ast_ctxt.extract(79 , 79 , op2));
    //             mskb.push(self.ast_ctxt.extract(71 , 71 , op2));
    //             mskb.push(self.ast_ctxt.extract(63 , 63 , op2));
    //             mskb.push(self.ast_ctxt.extract(55 , 55 , op2));
    //             mskb.push(self.ast_ctxt.extract(47 , 47 , op2));
    //             mskb.push(self.ast_ctxt.extract(39 , 39 , op2));
    //             mskb.push(self.ast_ctxt.extract(31 , 31 , op2));
    //             mskb.push(self.ast_ctxt.extract(23 , 23 , op2));
    //             mskb.push(self.ast_ctxt.extract(15 , 15 , op2));
    //             mskb.push(self.ast_ctxt.extract(7  , 7  , op2));
    //           }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::vpmovmskb_s(): Invalid operand size.");"#)
    //         }

    //         let node = self.ast_ctxt.zx(
    //                       dst.get_bit_size() - mskb.size() as u32,
    //                       self.ast_ctxt.concat(mskb)
    //                     );

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPMOVMSKB operation");

    //         /* Apply the taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpminub_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvuge(
    //                             self.ast_ctxt.extract(high, low, op1),
    //                             self.ast_ctxt.extract(high, low, op2)),
    //                           self.ast_ctxt.extract(high, low, op2),
    //                           self.ast_ctxt.extract(high, low, op1))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPMINUB operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpmulhw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           let n1 = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op1));
    //           let n2 = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op2));
    //           let node = self.ast_ctxt.extract(BitSizes::DWORD - 1, BitSizes::WORD, self.ast_ctxt.bvmul(n1, n2));
    //           pck.push(node);
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPMULHW operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpmullw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           let n1 = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op1));
    //           let n2 = self.ast_ctxt.sx(BitSizes::WORD, self.ast_ctxt.extract(high, low, op2));
    //           let node = self.ast_ctxt.extract(BitSizes::WORD - 1, 0, self.ast_ctxt.bvmul(n1, n2));
    //           pck.push(node);
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPMULLW operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpor_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvor(op2, op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPOR operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpshufd_s(&mut self, inst: x86Instruction) {
    //         let dst               = inst.operands[0];
    //         let src               = inst.operands[1];
    //         let ord               = inst.operands[2];
    //         let mut dstSize: u32 = dst.get_bit_size();

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, ord);

    //         /* Create the semantics */
    //         let mut pack: Vec<Instruction> = Vec::new();
    //         pack.reserve(8);

    //         match dstSize {

    //           /* YMM */
    //           BitSizes::QQWORD => {
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(7, 6, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(5, 4, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(3, 2, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(1, 0, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //         // todo: duplicated below

    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(7, 6, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(5, 4, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(3, 2, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(1, 0, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //         }

    //           /* XMM */
    //           BitSizes::DQWORD => {
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(7, 6, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(5, 4, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(3, 2, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             pack.push(
    //               self.ast_ctxt.extract(31, 0,
    //                 self.ast_ctxt.bvlshr(
    //                   op2,
    //                   self.ast_ctxt.bvmul(
    //                     self.ast_ctxt.zx(dstSize-2, self.ast_ctxt.extract(1, 0, op3)),
    //                     self.ast_ctxt.bv(32, dstSize)
    //                   )
    //                 )
    //               )
    //             );
    //             }

    //           _ => todo!(r#"triton::exceptions::Semantics("x86Semantics::vpshufd_s(): Invalid operand size.");"#)
    //         }

    //         let node = self.ast_ctxt.concat(pack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSHUFD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintAssignment(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsignw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           let val = self.ast_ctxt.extract(high, low, op2);
    //           pck.push(self.ast_ctxt.ite(
    //                           self.ast_ctxt.bvsgt(val, self.ast_ctxt.bv(0, BitSizes::WORD)),
    //                           self.ast_ctxt.extract(high, low, op1),
    //                           self.ast_ctxt.ite(
    //                             self.ast_ctxt.bvslt(val, self.ast_ctxt.bv(0, BitSizes::WORD)),
    //                             self.ast_ctxt.bvneg(self.ast_ctxt.extract(high, low, op1)),
    //                             self.ast_ctxt.bv(0, BitSizes::WORD)))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSIGNW operation");

    //         /* Spread taint */
    //         // self.taintEngine.setTaint(dst, false);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpslldq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.ast_ctxt.zx(BitSizes::DQWORD - src2.get_bit_size(), self.symbolicEngine.getOperandAst(inst, src2));

    //         /* Create the semantics */
    //         let mut node: Instruction;

    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DQWORD);

    //         for index in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DQWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DQWORD) - (index * BitSizes::DQWORD);
    //           pck.push(self.ast_ctxt.bvshl(
    //                          self.ast_ctxt.extract(high, low, op1),
    //                          self.ast_ctxt.bvmul(
    //                            self.ast_ctxt.ite(
    //                              self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::WORD, BitSizes::DQWORD)),
    //                              self.ast_ctxt.bv(BitSizes::WORD, BitSizes::DQWORD),
    //                              op2
    //                            ),
    //                            self.ast_ctxt.bv(BitSizes::BYTE, BitSizes::DQWORD)
    //                          )
    //                        ));
    //         }

    //         node = if pck.size() > 1 { self.ast_ctxt.concat(pck) } else{ pck[0] };

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSLLDQ operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsllw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         let shift = self.ast_ctxt.ite(
    //           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::WORD, src2.get_bit_size())),
    //           self.ast_ctxt.bv(BitSizes::WORD, src2.get_bit_size()),
    //           op2
    //         );

    //         if (shift.getBitvectorSize() < BitSizes::WORD) {
    //           shift = self.ast_ctxt.zx(BitSizes::WORD - shift.getBitvectorSize(), shift);
    //         }
    //         else {
    //           shift = self.ast_ctxt.extract(BitSizes::WORD - 1, 0, shift);
    //         }

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.bvshl(self.ast_ctxt.extract(high, low, op1), shift));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSLLW operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsrad_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         let shift = self.ast_ctxt.ite(
    //           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::DWORD, src2.get_bit_size())),
    //           self.ast_ctxt.bv(BitSizes::DWORD, src2.get_bit_size()),
    //           op2
    //         );

    //         if (shift.getBitvectorSize() < BitSizes::DWORD) {
    //           shift = self.ast_ctxt.zx(BitSizes::DWORD - shift.getBitvectorSize(), shift);
    //         }
    //         else {
    //           shift = self.ast_ctxt.extract(BitSizes::DWORD - 1, 0, shift);
    //         }

    //         for i in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (i * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.bvashr(self.ast_ctxt.extract(high, low, op1), shift));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSRAD operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsraw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         let shift = self.ast_ctxt.ite(
    //           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::WORD, src2.get_bit_size())),
    //           self.ast_ctxt.bv(BitSizes::WORD, src2.get_bit_size()),
    //           op2
    //         );

    //         if (shift.getBitvectorSize() < BitSizes::WORD) {
    //           shift = self.ast_ctxt.zx(BitSizes::WORD - shift.getBitvectorSize(), shift);
    //         }
    //         else {
    //           shift = self.ast_ctxt.extract(BitSizes::WORD - 1, 0, shift);
    //         }

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.bvashr(self.ast_ctxt.extract(high, low, op1), shift));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSRAW operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsrldq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DQWORD);

    //         let shift = self.ast_ctxt.ite(
    //           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::WORD, src2.get_bit_size())),
    //           self.ast_ctxt.bv(BitSizes::WORD, src2.get_bit_size()),
    //           op2
    //         );

    //         if (shift.getBitvectorSize() < BitSizes::DQWORD) {
    //           shift = self.ast_ctxt.zx(BitSizes::DQWORD - shift.getBitvectorSize(), shift);
    //         }
    //         else {
    //           shift = self.ast_ctxt.extract(BitSizes::DQWORD - 1, 0, shift);
    //         }
    //         shift = self.ast_ctxt.bvmul(shift, self.ast_ctxt.bv(BitSizes::BYTE, BitSizes::DQWORD));

    //         for i in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::DQWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DQWORD) - (i * BitSizes::DQWORD);
    //           pck.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(high, low, op1), shift));
    //         }
    //         let node = if pck.size() > 1 { self.ast_ctxt.concat(pck) } else {pck[0]};

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSRLDQ operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsrlw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         let shift = self.ast_ctxt.ite(
    //           self.ast_ctxt.bvuge(op2, self.ast_ctxt.bv(BitSizes::WORD, src2.get_bit_size())),
    //           self.ast_ctxt.bv(BitSizes::WORD, src2.get_bit_size()),
    //           op2
    //         );

    //         if (shift.getBitvectorSize() < BitSizes::WORD) {
    //           shift = self.ast_ctxt.zx(BitSizes::WORD - shift.getBitvectorSize(), shift);
    //         }
    //         else {
    //           shift = self.ast_ctxt.extract(BitSizes::WORD - 1, 0, shift);
    //         }

    //         for i in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (i * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (i * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.bvlshr(self.ast_ctxt.extract(high, low, op1), shift));
    //         }
    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSRLW operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsubb_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize());

    //         for index in 0..(dst.getSize()) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::BYTE);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::BYTE) - (index * BitSizes::BYTE);
    //           pck.push(self.ast_ctxt.bvsub(
    //                           self.ast_ctxt.extract(high, low, op1),
    //                           self.ast_ctxt.extract(high, low, op2))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSUBB operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsubd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::DWORD);

    //         for index in 0..(dst.getSize() / ByteSizes::DWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::DWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::DWORD) - (index * BitSizes::DWORD);
    //           pck.push(self.ast_ctxt.bvsub(
    //                          self.ast_ctxt.extract(high, low, op1),
    //                          self.ast_ctxt.extract(high, low, op2))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSUBD operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsubq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::QWORD);

    //         for index in 0..(dst.getSize() / ByteSizes::QWORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::QWORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::QWORD) - (index * BitSizes::QWORD);
    //           pck.push(self.ast_ctxt.bvsub(
    //                          self.ast_ctxt.extract(high, low, op1),
    //                          self.ast_ctxt.extract(high, low, op2))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSUBQ operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpsubw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut pck: Vec<Instruction> = Vec::new();
    //         pck.reserve(dst.getSize() / ByteSizes::WORD);

    //         for index in 0..(dst.getSize() / ByteSizes::WORD) {
    //           let high: u32 = (dst.get_bit_size() - 1) - (index * BitSizes::WORD);
    //           let low: u32 = (dst.get_bit_size() - BitSizes::WORD) - (index * BitSizes::WORD);
    //           pck.push(self.ast_ctxt.bvsub(
    //                          self.ast_ctxt.extract(high, low, op1),
    //                          self.ast_ctxt.extract(high, low, op2))
    //                        );
    //         }

    //         let node = self.ast_ctxt.concat(pck);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPSUBW operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vptest_s(&mut self, inst: x86Instruction) {
    //         let src1 = inst.operands[0];
    //         let src2 = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node1 = self.ast_ctxt.bvand(op1, op2);
    //         let node2 = self.ast_ctxt.bvand(op1, self.ast_ctxt.bvnot(op2));

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node1, "VPTEST operation");
    //         let expr2 = self.symbolicEngine.createSymbolicVolatileExpression(inst, node2, "VPTEST operation");

    //         /* Spread taint */
    //         // // expr1.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2);
    //         // // expr2.isTainted = self.taintEngine.isTainted(src1) | self.taintEngine.isTainted(src2);

    //         /* Update symbolic flags */
    //         self.clearFlag_s(inst, Register::AF, "Clears adjust flag");
    //         self.cfPtest_s(inst, expr2, src1, ); // todo: vol = true
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.clearFlag_s(inst, Register::PF, "Clears parity flag");
    //         self.clearFlag_s(inst, Register::SF, "Clears sign flag");
    //         self.zf_s(inst, expr1, src1, ); // todo: vol = true

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpunpckhbw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(dst.getSize());

    //         let start_index: u32 = dst.get_bit_size();
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           start_index -= k * BitSizes::DQWORD;
    //           for i in 0..(ByteSizes::DQWORD / ByteSizes::WORD) {
    //             let high: u32 = (start_index - 1) - (i * BitSizes::BYTE);
    //             let low: u32 = (start_index - BitSizes::BYTE) - (i * BitSizes::BYTE);
    //             unpack.push(self.ast_ctxt.extract(high, low, op2));
    //             unpack.push(self.ast_ctxt.extract(high, low, op1));
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPUNPCKHBW operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpunpckhdq_s(&mut self, inst: x86Instruction)  {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(dst.getSize() / ByteSizes::DWORD);

    //         let start_index: u32 = dst.get_bit_size();
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           start_index -= k * BitSizes::DQWORD;
    //           for i in 0..(ByteSizes::DQWORD / ByteSizes::QWORD) {
    //             let high: u32 = (start_index - 1) - (i * BitSizes::DWORD);
    //             let low: u32 = (start_index - BitSizes::DWORD) - (i * BitSizes::DWORD);
    //             unpack.push(self.ast_ctxt.extract(high, low, op2));
    //             unpack.push(self.ast_ctxt.extract(high, low, op1));
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPUNPCKHDQ operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpunpckhqdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(dst.getSize() / ByteSizes::QWORD);

    //         let start_index: u32 = dst.get_bit_size();
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           start_index -= k * BitSizes::DQWORD;
    //           for i in 0..(ByteSizes::DQWORD / ByteSizes::DQWORD) {
    //             let high: u32 = (start_index - 1) - (i * BitSizes::QWORD);
    //             let low: u32 = (start_index - BitSizes::QWORD) - (i * BitSizes::QWORD);
    //             unpack.push(self.ast_ctxt.extract(high, low, op2));
    //             unpack.push(self.ast_ctxt.extract(high, low, op1));
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPUNPCKHQDQ operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpunpckhwd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(dst.getSize() / ByteSizes::WORD);

    //         let start_index: u32 = dst.get_bit_size();
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           start_index -= k * BitSizes::DQWORD;
    //           for i in 0..(ByteSizes::DQWORD / ByteSizes::DWORD) {
    //             let high: u32 = (start_index - 1) - (i * BitSizes::WORD);
    //             let low: u32 = (start_index - BitSizes::WORD) - (i * BitSizes::WORD);
    //             unpack.push(self.ast_ctxt.extract(high, low, op2));
    //             unpack.push(self.ast_ctxt.extract(high, low, op1));
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPUNPCKHWD operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpunpcklbw_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(dst.getSize());

    //         let start_index: u32 = dst.get_bit_size() - BitSizes::QWORD;
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           start_index -= k * BitSizes::DQWORD;
    //           for i in 0..(ByteSizes::DQWORD / ByteSizes::WORD) {
    //             let high: u32 = (start_index - 1) - (i * BitSizes::BYTE);
    //             let low: u32 = (start_index - BitSizes::BYTE) - (i * BitSizes::BYTE);
    //             unpack.push(self.ast_ctxt.extract(high, low, op2));
    //             unpack.push(self.ast_ctxt.extract(high, low, op1));
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPUNPCKLBW operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpunpckldq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(dst.getSize() / ByteSizes::DWORD);

    //         let start_index: u32 = dst.get_bit_size() - BitSizes::QWORD;
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           start_index -= k * BitSizes::DQWORD;
    //           for i in 0..(ByteSizes::DQWORD / ByteSizes::QWORD) {
    //             let high: u32 = (start_index - 1) - (i * BitSizes::DWORD);
    //             let low: u32 = (start_index - BitSizes::DWORD) - (i * BitSizes::DWORD);
    //             unpack.push(self.ast_ctxt.extract(high, low, op2));
    //             unpack.push(self.ast_ctxt.extract(high, low, op1));
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPUNPCKLDQ operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpunpcklqdq_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(dst.getSize() / ByteSizes::QWORD);

    //         let start_index: u32 = dst.get_bit_size() - BitSizes::QWORD;
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           start_index -= k * BitSizes::DQWORD;
    //           for i in 0..(ByteSizes::DQWORD / ByteSizes::DQWORD) {
    //             let high: u32 = (start_index - 1) - (i * BitSizes::QWORD);
    //             let low: u32 = (start_index - BitSizes::QWORD) - (i * BitSizes::QWORD);
    //             unpack.push(self.ast_ctxt.extract(high, low, op2));
    //             unpack.push(self.ast_ctxt.extract(high, low, op1));
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPUNPCKLQDQ operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpunpcklwd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let mut unpack: Vec<Instruction> = Vec::new();
    //         unpack.reserve(dst.getSize() / ByteSizes::WORD);

    //         let start_index: u32 = dst.get_bit_size() - BitSizes::QWORD;
    //         for k in 0..(dst.getSize() / ByteSizes::DQWORD) {
    //           start_index -= k * BitSizes::DQWORD;
    //           for i in 0..(ByteSizes::DQWORD / ByteSizes::DWORD) {
    //             let high: u32 = (start_index - 1) - (i * BitSizes::WORD);
    //             let low: u32 = (start_index - BitSizes::WORD) - (i * BitSizes::WORD);
    //             unpack.push(self.ast_ctxt.extract(high, low, op2));
    //             unpack.push(self.ast_ctxt.extract(high, low, op1));
    //           }
    //         }

    //         let node = self.ast_ctxt.concat(unpack);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPUNPCKLWD operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vpxor_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op3 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvxor(op2, op3);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VPXOR operation");

    //         /* Spread taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn vxorps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src1 = inst.operands[1];
    //         let src2 = inst.operands[2];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, src1);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src2);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvxor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "VXORPS operation");

    //         /* Apply the taint */
    //         // // expr.isTainted = self.taintEngine.taintAssignment(dst, src1) | self.taintEngine.taintUnion(dst, src2);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn wait_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn wbinvd_s(&mut self, inst: x86Instruction) {
    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn xadd_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src  = inst.operands[1];
    //         // let mut dstT: bool = self.taintEngine.isTainted(dst);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvadd(op1, op2);

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, op1, src, "XADD operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "XADD operation");

    //         /* Spread taint */
    //         // expr2.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // expr1.isTainted = self.taintEngine.setTaint(src, dstT);

    //         /* Update symbolic flags */
    //         self.af_s(inst, expr2, dst, op1, op2);
    //         self.cfAdd_s(inst, expr2, dst, op1, op2);
    //         self.ofAdd_s(inst, expr2, dst, op1, op2);
    //         self.pf_s(inst, expr2, dst);
    //         self.sf_s(inst, expr2, dst);
    //         self.zf_s(inst, expr2, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn xchg_s(&mut self, inst: x86Instruction) {
    //         let dst  = inst.operands[0];
    //         let src  = inst.operands[1];
    //         // let mut dstT: bool = self.taintEngine.isTainted(dst);
    //         // let mut srcT: bool = self.taintEngine.isTainted(src);

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node1 = op2;
    //         let node2 = op1;

    //         /* Create symbolic expression */
    //         let expr1 = self.symbolicEngine.createSymbolicExpression(inst, node1, dst, "XCHG operation");
    //         let expr2 = self.symbolicEngine.createSymbolicExpression(inst, node2, src, "XCHG operation");

    //         /* Spread taint */
    //         // expr1.isTainted = self.taintEngine.setTaint(dst, srcT);
    //         // expr2.isTainted = self.taintEngine.setTaint(src, dstT);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn xor_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvxor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "XOR operation");

    //         /* Spread taint */
    //         /* clear taint if the registers are the same */
    //         // if (dst.getType() == OP_REG && src.getRegister() == dst.getRegister()){
    //         //   self.taintEngine.setTaint(src, false);
    //         // }else{
    //         //   expr.isTainted = self.taintEngine.taintUnion(dst, src);
    //         // }
    //         /* Update symbolic flags */
    //         self.undefined_s(inst, Register::AF);
    //         self.clearFlag_s(inst, Register::CF, "Clears carry flag");
    //         self.clearFlag_s(inst, Register::OF, "Clears overflow flag");
    //         self.pf_s(inst, expr, dst);
    //         self.sf_s(inst, expr, dst);
    //         self.zf_s(inst, expr, dst);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn xorpd_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvxor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "XORPD operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }

    //       fn xorps_s(&mut self, inst: x86Instruction) {
    //         let dst = inst.operands[0];
    //         let src = inst.operands[1];

    //         /* Create symbolic operands */
    //         let op1 = self.symbolicEngine.getOperandAst(inst, dst);
    //         let op2 = self.symbolicEngine.getOperandAst(inst, src);

    //         /* Create the semantics */
    //         let node = self.ast_ctxt.bvxor(op1, op2);

    //         /* Create symbolic expression */
    //         let expr = self.symbolicEngine.createSymbolicExpression(inst, node, dst, "XORPS operation");

    //         /* Spread taint */
    //         // expr.isTainted = self.taintEngine.taintUnion(dst, src);

    //         /* Update the symbolic control flow */
    //         self.controlFlow_s(inst);
    //       }
}
