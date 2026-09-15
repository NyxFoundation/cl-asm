import ClAsm.Rv64

namespace ClAsm.Codegen

open ClAsm.Rv64

def emitReg (reg : Reg) : String :=
  reg.abiName

private def emitMem (offset : Int) (base : Reg) : String :=
  toString offset ++ "(" ++ emitReg base ++ ")"

def emitInstr : Instr -> String
  | .label name => name ++ ":"
  | .comment text => "  # " ++ text
  | .raw asm => asm
  | .li rd imm => "  li " ++ emitReg rd ++ ", " ++ toString imm
  | .la rd symbol => "  la " ++ emitReg rd ++ ", " ++ symbol
  | .mv rd rs => "  mv " ++ emitReg rd ++ ", " ++ emitReg rs
  | .add rd rs1 rs2 => "  add " ++ emitReg rd ++ ", " ++ emitReg rs1 ++ ", " ++ emitReg rs2
  | .addi rd rs1 imm => "  addi " ++ emitReg rd ++ ", " ++ emitReg rs1 ++ ", " ++ toString imm
  | .sub rd rs1 rs2 => "  sub " ++ emitReg rd ++ ", " ++ emitReg rs1 ++ ", " ++ emitReg rs2
  | .slli rd rs shamt => "  slli " ++ emitReg rd ++ ", " ++ emitReg rs ++ ", " ++ toString shamt
  | .srli rd rs shamt => "  srli " ++ emitReg rd ++ ", " ++ emitReg rs ++ ", " ++ toString shamt
  | .andi rd rs imm => "  andi " ++ emitReg rd ++ ", " ++ emitReg rs ++ ", " ++ toString imm
  | .ori rd rs imm => "  ori " ++ emitReg rd ++ ", " ++ emitReg rs ++ ", " ++ toString imm
  | .ld rd base offset => "  ld " ++ emitReg rd ++ ", " ++ emitMem offset base
  | .sd rs base offset => "  sd " ++ emitReg rs ++ ", " ++ emitMem offset base
  | .lbu rd base offset => "  lbu " ++ emitReg rd ++ ", " ++ emitMem offset base
  | .sb rs base offset => "  sb " ++ emitReg rs ++ ", " ++ emitMem offset base
  | .beq rs1 rs2 target => "  beq " ++ emitReg rs1 ++ ", " ++ emitReg rs2 ++ ", " ++ target
  | .bne rs1 rs2 target => "  bne " ++ emitReg rs1 ++ ", " ++ emitReg rs2 ++ ", " ++ target
  | .bltu rs1 rs2 target => "  bltu " ++ emitReg rs1 ++ ", " ++ emitReg rs2 ++ ", " ++ target
  | .j target => "  j " ++ target
  | .ret => "  ret"
  | .ecall => "  ecall"

def emitProgramLines (program : Program) : List String :=
  program.map emitInstr

private def joinLines : List String -> String
  | [] => ""
  | [line] => line
  | line :: rest => line ++ "\n" ++ joinLines rest

def emitProgram (program : Program) : String :=
  joinLines (emitProgramLines program)

end ClAsm.Codegen
