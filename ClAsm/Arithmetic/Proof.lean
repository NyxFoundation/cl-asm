import ClAsm.Arithmetic
import RiscvZkvm.Rv64.Logic.SyscallSpecs
import RiscvZkvm.Rv64.Logic.Tactics.RunBlock
import RiscvZkvm.Rv64.Logic.AddrNorm

namespace ClAsm.Arithmetic

open RiscvZkvm.Rv64

theorem previousEpoch_spec (src dst : Reg) (base epoch oldDst : Word)
    (hdst : dst ≠ .x0) (_hne : src ≠ dst) :
    cpsTripleWithin (previousEpoch src dst).length base (base + 12)
      (CodeReq.ofProg base (previousEpoch src dst))
      ((src ↦ᵣ epoch) ** (dst ↦ᵣ oldDst))
      ((src ↦ᵣ epoch) ** (dst ↦ᵣ previousValue epoch)) := by
  unfold previousEpoch previousValue
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  runBlock

theorem shiftJustificationBits_spec (reg : Reg) (base bits : Word) (hreg : reg ≠ .x0) :
    cpsTripleWithin (shiftJustificationBits reg).length base (base + 8)
      (CodeReq.ofProg base (shiftJustificationBits reg))
      (reg ↦ᵣ bits) (reg ↦ᵣ shiftedBits bits) := by
  unfold shiftJustificationBits shiftedBits
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have shift : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SLLI reg reg 1))
      (reg ↦ᵣ bits) (reg ↦ᵣ bits <<< (1 : Nat)) := by
    simpa using slli_spec_gen_same_within reg bits 1 base hreg
  have mask : cpsTripleWithin 1 (base + 4) (base + 4 + 4)
      (CodeReq.singleton (base + 4) (.ANDI reg reg 15))
      (reg ↦ᵣ bits <<< (1 : Nat)) (reg ↦ᵣ (bits <<< (1 : Nat)) &&& 15) := by
    simpa [signExtend12] using andi_spec_gen_same_within reg (bits <<< (1 : Nat)) 15 (base + 4) hreg
  runBlock shift mask

theorem hasSupermajority_spec (vote total triple twice : Reg)
    (base a t oldTriple oldTwice : Word) (htriple : triple ≠ .x0) (htwice : twice ≠ .x0)
    (_hdistinct : [vote, total, triple, twice].Nodup) :
    cpsTripleWithin (hasSupermajority vote total triple twice).length base (base + 20)
      (CodeReq.ofProg base (hasSupermajority vote total triple twice))
      ((vote ↦ᵣ a) ** (total ↦ᵣ t) ** (triple ↦ᵣ oldTriple) ** (twice ↦ᵣ oldTwice))
      ((vote ↦ᵣ a) ** (total ↦ᵣ t) ** (triple ↦ᵣ thresholdValue a t) ** (twice ↦ᵣ t <<< (1 : Nat))) := by
  unfold hasSupermajority thresholdValue
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SLLI triple vote 1))
      ((vote ↦ᵣ a) ** (triple ↦ᵣ oldTriple))
      ((vote ↦ᵣ a) ** (triple ↦ᵣ a <<< (1 : Nat))) := by
    simpa using slli_spec_gen_within triple vote oldTriple a 1 base htriple
  have s2 := add_spec_gen_rd_eq_rs1_within triple vote (a <<< (1 : Nat)) a (base + 4) htriple
  have s3 : cpsTripleWithin 1 (base + 8) (base + 8 + 4)
      (CodeReq.singleton (base + 8) (.SLLI twice total 1))
      ((total ↦ᵣ t) ** (twice ↦ᵣ oldTwice))
      ((total ↦ᵣ t) ** (twice ↦ᵣ t <<< (1 : Nat))) := by
    simpa using slli_spec_gen_within twice total oldTwice t 1 (base + 8) htwice
  have s4 := sltu_spec_gen_rd_eq_rs1_within triple twice
    ((a <<< (1 : Nat)) + a) (t <<< (1 : Nat)) (base + 12) htriple
  have s5 : cpsTripleWithin 1 (base + 16) (base + 16 + 4)
      (CodeReq.singleton (base + 16) (.XORI triple triple 1))
      (triple ↦ᵣ (if BitVec.ult ((a <<< (1 : Nat)) + a) (t <<< (1 : Nat)) then 1 else 0))
      (triple ↦ᵣ (if BitVec.ult ((a <<< (1 : Nat)) + a) (t <<< (1 : Nat)) then 1 else 0) ^^^ 1) := by
    simpa [signExtend12] using xori_spec_gen_same_within triple
      (if BitVec.ult ((a <<< (1 : Nat)) + a) (t <<< (1 : Nat)) then 1 else 0) 1 (base + 16) htriple
  runBlock s1 s2 s3 s4 s5

theorem blockRootAddress_spec (epoch roots dst : Reg) (base e ptr oldDst : Word)
    (hdst : dst ≠ .x0) (_hdistinct : [epoch, roots, dst].Nodup) :
    cpsTripleWithin (blockRootAddress epoch roots dst).length base (base + 12)
      (CodeReq.ofProg base (blockRootAddress epoch roots dst))
      ((epoch ↦ᵣ e) ** (roots ↦ᵣ ptr) ** (dst ↦ᵣ oldDst))
      ((epoch ↦ᵣ e) ** (roots ↦ᵣ ptr) ** (dst ↦ᵣ ptr + rootOffset e)) := by
  unfold blockRootAddress rootOffset
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  runBlock

end ClAsm.Arithmetic
