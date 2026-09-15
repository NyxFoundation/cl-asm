namespace ClAsm.Rv64

inductive Reg where
  | zero
  | ra
  | sp
  | gp
  | tp
  | t0
  | t1
  | t2
  | s0
  | s1
  | a0
  | a1
  | a2
  | a3
  | a4
  | a5
  | a6
  | a7
  | s2
  | s3
  | s4
  | s5
  | s6
  | s7
  | s8
  | s9
  | s10
  | s11
  | t3
  | t4
  | t5
  | t6
deriving DecidableEq, Repr

def Reg.abiName : Reg -> String
  | .zero => "zero"
  | .ra => "ra"
  | .sp => "sp"
  | .gp => "gp"
  | .tp => "tp"
  | .t0 => "t0"
  | .t1 => "t1"
  | .t2 => "t2"
  | .s0 => "s0"
  | .s1 => "s1"
  | .a0 => "a0"
  | .a1 => "a1"
  | .a2 => "a2"
  | .a3 => "a3"
  | .a4 => "a4"
  | .a5 => "a5"
  | .a6 => "a6"
  | .a7 => "a7"
  | .s2 => "s2"
  | .s3 => "s3"
  | .s4 => "s4"
  | .s5 => "s5"
  | .s6 => "s6"
  | .s7 => "s7"
  | .s8 => "s8"
  | .s9 => "s9"
  | .s10 => "s10"
  | .s11 => "s11"
  | .t3 => "t3"
  | .t4 => "t4"
  | .t5 => "t5"
  | .t6 => "t6"

inductive Instr where
  | label (name : String)
  | comment (text : String)
  | raw (asm : String)
  | li (rd : Reg) (imm : Int)
  | la (rd : Reg) (symbol : String)
  | mv (rd rs : Reg)
  | add (rd rs1 rs2 : Reg)
  | addi (rd rs1 : Reg) (imm : Int)
  | sub (rd rs1 rs2 : Reg)
  | slli (rd rs : Reg) (shamt : Nat)
  | srli (rd rs : Reg) (shamt : Nat)
  | andi (rd rs : Reg) (imm : Int)
  | ori (rd rs : Reg) (imm : Int)
  | ld (rd base : Reg) (offset : Int)
  | sd (rs base : Reg) (offset : Int)
  | lbu (rd base : Reg) (offset : Int)
  | sb (rs base : Reg) (offset : Int)
  | beq (rs1 rs2 : Reg) (target : String)
  | bne (rs1 rs2 : Reg) (target : String)
  | bltu (rs1 rs2 : Reg) (target : String)
  | j (target : String)
  | ret
  | ecall
deriving DecidableEq, Repr

abbrev Program := List Instr

end ClAsm.Rv64
