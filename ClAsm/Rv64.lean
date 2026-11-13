import LeanAsm.Frontend
import RiscvZkvm.Rv64.Program

/-! Temporary syntax adapter while cl-asm proofs are ported to LeanAsm. -/

namespace ClAsm.Rv64

namespace Upstream

open RiscvZkvm.Rv64

private def reg : Reg → LeanAsm.Rv64.Reg
  | .x0 => .x0 | .x1 => .x1 | .x2 => .x2 | .x3 => .x3
  | .x4 => .x4 | .x5 => .x5 | .x6 => .x6 | .x7 => .x7
  | .x8 => .x8 | .x9 => .x9 | .x10 => .x10 | .x11 => .x11
  | .x12 => .x12 | .x13 => .x13 | .x14 => .x14 | .x15 => .x15
  | .x16 => .x16 | .x17 => .x17 | .x18 => .x18 | .x19 => .x19
  | .x20 => .x20 | .x21 => .x21 | .x22 => .x22 | .x23 => .x23
  | .x24 => .x24 | .x25 => .x25 | .x26 => .x26 | .x27 => .x27
  | .x28 => .x28 | .x29 => .x29 | .x30 => .x30 | .x31 => .x31

def instr : Instr → Except String LeanAsm.Rv64.Instr
  | .ADD d a b => .ok (.ADD (reg d) (reg a) (reg b))
  | .SUB d a b => .ok (.SUB (reg d) (reg a) (reg b))
  | .SLL d a b => .ok (.SLL (reg d) (reg a) (reg b))
  | .SRL d a b => .ok (.SRL (reg d) (reg a) (reg b))
  | .SRA d a b => .ok (.SRA (reg d) (reg a) (reg b))
  | .AND d a b => .ok (.AND (reg d) (reg a) (reg b))
  | .OR d a b => .ok (.OR (reg d) (reg a) (reg b))
  | .XOR d a b => .ok (.XOR (reg d) (reg a) (reg b))
  | .SLT d a b => .ok (.SLT (reg d) (reg a) (reg b))
  | .SLTU d a b => .ok (.SLTU (reg d) (reg a) (reg b))
  | .ADDI d a n => .ok (.ADDI (reg d) (reg a) n)
  | .ANDI d a n => .ok (.ANDI (reg d) (reg a) n)
  | .ORI d a n => .ok (.ORI (reg d) (reg a) n)
  | .XORI d a n => .ok (.XORI (reg d) (reg a) n)
  | .SLTI d a n => .ok (.SLTI (reg d) (reg a) n)
  | .SLTIU d a n => .ok (.SLTIU (reg d) (reg a) n)
  | .SLLI d a n => .ok (.SLLI (reg d) (reg a) n)
  | .SRLI d a n => .ok (.SRLI (reg d) (reg a) n)
  | .SRAI d a n => .ok (.SRAI (reg d) (reg a) n)
  | .LUI d n => .ok (.LUI (reg d) n)
  | .AUIPC d n => .ok (.AUIPC (reg d) n)
  | .LD d a n => .ok (.LD (reg d) (reg a) n)
  | .SD a b n => .ok (.SD (reg a) (reg b) n)
  | .LW d a n => .ok (.LW (reg d) (reg a) n)
  | .LWU d a n => .ok (.LWU (reg d) (reg a) n)
  | .SW a b n => .ok (.SW (reg a) (reg b) n)
  | .LB d a n => .ok (.LB (reg d) (reg a) n)
  | .LH d a n => .ok (.LH (reg d) (reg a) n)
  | .LBU d a n => .ok (.LBU (reg d) (reg a) n)
  | .LHU d a n => .ok (.LHU (reg d) (reg a) n)
  | .SB a b n => .ok (.SB (reg a) (reg b) n)
  | .SH a b n => .ok (.SH (reg a) (reg b) n)
  | .BEQ a b n => .ok (.BEQ (reg a) (reg b) n)
  | .BNE a b n => .ok (.BNE (reg a) (reg b) n)
  | .BLT a b n => .ok (.BLT (reg a) (reg b) n)
  | .BGE a b n => .ok (.BGE (reg a) (reg b) n)
  | .BLTU a b n => .ok (.BLTU (reg a) (reg b) n)
  | .BGEU a b n => .ok (.BGEU (reg a) (reg b) n)
  | .JAL d n => .ok (.JAL (reg d) n)
  | .JALR d a n => .ok (.JALR (reg d) (reg a) n)
  | .ADDIW d a n => .ok (.ADDIW (reg d) (reg a) n)
  | .FENCE => .ok .FENCE
  | .MUL d a b => .ok (.MUL (reg d) (reg a) (reg b))
  | .MULH d a b => .ok (.MULH (reg d) (reg a) (reg b))
  | .MULHSU d a b => .ok (.MULHSU (reg d) (reg a) (reg b))
  | .MULHU d a b => .ok (.MULHU (reg d) (reg a) (reg b))
  | .DIV d a b => .ok (.DIV (reg d) (reg a) (reg b))
  | .DIVU d a b => .ok (.DIVU (reg d) (reg a) (reg b))
  | .REM d a b => .ok (.REM (reg d) (reg a) (reg b))
  | .REMU d a b => .ok (.REMU (reg d) (reg a) (reg b))
  | _ => .error "instruction has no portable LeanAsm representation"

/-- Opcodes accepted by the portable cl-asm code-generation boundary. -/
def isaProfile : LeanAsm.Rv64.IsaProfile :=
  ⟨[.ADD, .SUB, .SLL, .SRL, .SRA, .AND, .OR, .XOR, .SLT, .SLTU,
    .ADDI, .ANDI, .ORI, .XORI, .SLTI, .SLTIU, .SLLI, .SRLI, .SRAI,
    .ADDIW, .LUI, .AUIPC,
    .LB, .LH, .LW, .LD, .LBU, .LHU, .LWU, .SB, .SH, .SW, .SD,
    .BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU, .JAL, .JALR,
    .MUL, .MULH, .MULHSU, .MULHU, .DIV, .DIVU, .REM, .REMU, .FENCE]⟩

def program (source : Program) : Except String LeanAsm.Rv64.Program :=
  source.mapM instr

instance : LeanAsm.LowerRv64 Program where
  lower := program

instance : LeanAsm.EmitAsm Program where
  emit name source := do
    let target ← program source
    return LeanAsm.Rv64.emitProgram name target

end Upstream
end ClAsm.Rv64
