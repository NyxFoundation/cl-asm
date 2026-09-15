import ClAsm.Weigh.Roots
import ClAsm.Weigh.Contract
import ClAsm.Weigh.Branch
import ClAsm.Arithmetic.Meaning

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

theorem rootOffset_eq (e : Word) :
    Arithmetic.rootOffset e = BitVec.ofNat 64 (rootIndex e.toNat * 32) := by
  unfold rootIndex Layout.slotsPerEpoch Layout.slotsPerHistoricalRoot
  rw [← Arithmetic.rootOffset_toNat]
  simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem justifyBody_spec (base ptr array e bits oldSource oldTarget oldTmp : Word)
    (epochReg : Reg) (bit : BitVec 12) (roots : List Root) (old : Checkpoint)
    (hindex : rootIndex e.toNat < roots.length) (hdistinct : [epochReg, .x11, .x6].Nodup) :
    cpsTripleWithin (justifyBody epochReg bit).length base (base + 56)
      (CodeReq.ofProg base (justifyBody epochReg bit))
      ((epochReg ↦ᵣ e) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ array) ** (.x28 ↦ᵣ bits) **
        (.x6 ↦ᵣ oldSource) ** (.x7 ↦ᵣ oldTarget) ** (.x5 ↦ᵣ oldTmp) **
        rootsOwn array roots ** old.owns (ptr + 56))
      ((epochReg ↦ᵣ e) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ array) **
        (.x28 ↦ᵣ bits ||| signExtend12 bit) ** (.x6 ↦ᵣ array + Arithmetic.rootOffset e) **
        (.x7 ↦ᵣ ptr + 64) ** (.x5 ↦ᵣ roots[rootIndex e.toNat].w3) **
        rootsOwn array roots ** (Checkpoint.mk e roots[rootIndex e.toNat]).owns (ptr + 56)) := by
  haveI : Assertion.PCFree (rootsOwn array roots) := ⟨rootsOwn_pcFree array roots⟩
  have store := sd_spec_within .x10 epochReg ptr e old.epoch 56 base
  have address := Arithmetic.blockRootAddress_spec epochReg .x11 .x6 (base + 4)
    e array oldSource (by decide) hdistinct
  have target := addi_spec_gen_within .x7 .x10 oldTarget ptr 64 (base + 16) (by decide)
  have copy := copyRoot_fromArray_spec (base + 20) array (ptr + 64) oldTmp
    roots (rootIndex e.toNat) hindex old.root
  rw [← rootOffset_eq] at copy
  have setBit := ori_spec_gen_same_within .x28 bits bit (base + 52) (by decide)
  simp only [justifyBody, Arithmetic.blockRootAddress, copyRoot, Root.owns, Checkpoint.owns,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    CodeReq.ofProg_cons, CodeReq.ofProg_nil] at address copy ⊢
  runBlock store address target copy setBit

def justificationVote (balances : Balances) (current : Bool) : Word :=
  if current then balances.current else balances.previous

def justificationEpoch (r : Registers) (current : Bool) : Word :=
  if current then r.prologue.epoch else r.prologue.previousEpoch

def justificationBit (current : Bool) : BitVec 12 := if current then 1 else 2

def justificationValue (balances : Balances) (current : Bool) : Word :=
  Arithmetic.thresholdValue (justificationVote balances current) balances.total

def justifiedCheckpoint (balances : Balances) (r : Registers) (roots : RootArray)
    (current : Bool) (old : Checkpoint) : Checkpoint :=
  if justificationValue balances current = 0 then old else
    ⟨justificationEpoch r current, roots.at (rootIndex (justificationEpoch r current).toNat)⟩

def justifyRegisters (a : Addresses) (balances : Balances) (r : Registers) (roots : RootArray)
    (current : Bool) : Registers :=
  { r with
    predicate := justificationValue balances current
    twiceTotal := balances.total <<< (1 : Nat)
    prologue := if justificationValue balances current = 0 then r.prologue else
      { r.prologue with
        temporary := (roots.at (rootIndex (justificationEpoch r current).toNat)).w3
        source := a.roots + Arithmetic.rootOffset (justificationEpoch r current)
        target := a.state + 64
        bits := r.prologue.bits ||| signExtend12 (justificationBit current) } }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem justify_spec (base : Word) (a : Addresses) (balances : Balances) (r : Registers)
    (roots : RootArray) (old : Checkpoint) (current : Bool) :
    cpsTripleWithin 21 base (base + 84)
      (CodeReq.ofProg base (justify (if current then .x14 else .x13)
        (if current then .x16 else .x17) (justificationBit current)))
      (r.owns a balances ** rootsOwn a.roots (List.ofFn roots) ** old.owns (a.state + 56))
      ((justifyRegisters a balances r roots current).owns a balances **
        rootsOwn a.roots (List.ofFn roots) **
        (justifiedCheckpoint balances r roots current old).owns (a.state + 56)) := by
  haveI : Assertion.PCFree (rootsOwn a.roots (List.ofFn roots)) :=
    ⟨rootsOwn_pcFree a.roots (List.ofFn roots)⟩
  have hi : rootIndex (justificationEpoch r current).toNat < (List.ofFn roots).length := by
    simp only [List.length_ofFn, rootIndex]
    exact Nat.mod_lt _ (by decide)
  have condition := Arithmetic.hasSupermajority_spec (if current then .x14 else .x13)
    .x12 .x29 .x30 base (justificationVote balances current) balances.total
    r.predicate r.twiceTotal (by decide) (by decide) (by cases current <;> decide)
  have branch := branchNonzero_spec (base + 20) (justificationValue balances current)
  have skip := jal_x0_spec_gen_within 60 (base + 24)
  simp only [show signExtend21 (60 : BitVec 21) = (60 : Word) from by decide] at skip
  have body := justifyBody_spec (base + 28) a.state a.roots (justificationEpoch r current)
    r.prologue.bits r.prologue.source r.prologue.target r.prologue.temporary
    (if current then .x16 else .x17) (justificationBit current) (List.ofFn roots) old hi
    (by cases current <;> decide)
  have hr : (List.ofFn roots)[rootIndex (justificationEpoch r current).toNat] =
      roots.at (rootIndex (justificationEpoch r current).toNat) := by
    simp [RootArray.at, Nat.mod_eq_of_lt (by simpa using hi)]
  simp only [hr] at body
  unfold justifyRegisters justifiedCheckpoint Registers.owns PrologueRegisters.owns
  simp only [justify, justifyBody, Arithmetic.hasSupermajority, Arithmetic.blockRootAddress,
    if_eq, copyRoot, Checkpoint.owns, List.cons_append, List.nil_append,
    List.length_cons, List.length_nil, CodeReq.ofProg_cons, CodeReq.ofProg_nil] at condition body ⊢
  by_cases h : justificationValue balances current = 0
  · have hv : Arithmetic.thresholdValue (justificationVote balances current) balances.total = 0 := h
    simp only [hv] at condition
    simp only [h, if_true] at branch ⊢
    cases current <;> simp only [justificationVote, justificationEpoch, justificationBit,
      Bool.false_eq_true, if_false, if_true] at condition body ⊢ <;> runBlock condition branch skip
  · simp only [h, if_false] at branch ⊢
    cases current <;> simp only [justificationValue, justificationVote, justificationEpoch,
      justificationBit, Bool.false_eq_true, if_false, if_true] at condition branch body ⊢ <;>
      runBlock condition branch body

end ClAsm.Weigh
