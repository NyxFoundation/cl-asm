import ClAsm.Weigh.State
import ClAsm.Checkpoint.Proof

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

/-- The untouched array cells when borrowing one root. -/
def rootsWithout (base : Word) (roots : List Root) (index : Nat) : Assertion :=
  match roots, index with
  | [], _ => empAssertion
  | _ :: tail, 0 => rootsOwn (base + 32) tail
  | root :: tail, n + 1 => root.owns base ** rootsWithout (base + 32) tail n

theorem rootsOwn_pcFree (base : Word) (roots : List Root) : (rootsOwn base roots).pcFree := by
  induction roots generalizing base with
  | nil => exact pcFree_emp
  | cons root tail ih =>
    exact pcFree_sepConj (by unfold Root.owns; pcFree) (ih (base + 32))

theorem rootsWithout_pcFree (base : Word) (roots : List Root) (index : Nat) :
    (rootsWithout base roots index).pcFree := by
  induction roots generalizing base index with
  | nil => exact pcFree_emp
  | cons root tail ih =>
    cases index with
    | zero => exact rootsOwn_pcFree (base + 32) tail
    | succ n => exact pcFree_sepConj (by unfold Root.owns; pcFree) (ih (base + 32) n)

/-- Borrow and reassemble a single selected root; no second-root disjointness
    is needed when previous and current epoch coincide at genesis. -/
theorem rootsOwn_extract (base : Word) (roots : List Root) (index : Nat) (h : index < roots.length) :
    rootsOwn base roots =
      (roots[index].owns (base + BitVec.ofNat 64 (index * 32)) ** rootsWithout base roots index) := by
  induction roots generalizing base index with
  | nil => simp at h
  | cons root tail ih =>
    cases index with
    | zero => simp [rootsOwn, rootsWithout]
    | succ n =>
      have hn : n < tail.length := by simpa using h
      rw [rootsOwn, rootsWithout, ih (base + 32) n hn]
      have address : base + 32 + BitVec.ofNat 64 (n * 32) =
          base + BitVec.ofNat 64 ((n + 1) * 32) := by
        simp only [Nat.add_mul, Nat.one_mul, BitVec.ofNat_add, BitVec.add_assoc]
        congr 1
        exact BitVec.add_comm _ _
      rw [address]
      exact sepConj_left_comm' _ _ _

theorem copyRoot_fromArray_spec (base array target oldTmp : Word) (roots : List Root)
    (index : Nat) (h : index < roots.length) (old : Root) :
    cpsTripleWithin (copyRoot .x6 .x7 .x5).length base (base + 32)
      (CodeReq.ofProg base (copyRoot .x6 .x7 .x5))
      ((.x6 ↦ᵣ array + BitVec.ofNat 64 (index * 32)) ** (.x7 ↦ᵣ target) ** (.x5 ↦ᵣ oldTmp) **
        rootsOwn array roots ** old.owns target)
      ((.x6 ↦ᵣ array + BitVec.ofNat 64 (index * 32)) ** (.x7 ↦ᵣ target) ** (.x5 ↦ᵣ roots[index].w3) **
        rootsOwn array roots ** roots[index].owns target) := by
  rw [rootsOwn_extract array roots index h]
  have body := copyRoot_spec .x6 .x7 .x5 base (array + BitVec.ofNat 64 (index * 32))
    target oldTmp roots[index] old (by decide) (by decide)
  haveI : Assertion.PCFree (rootsWithout array roots index) := ⟨rootsWithout_pcFree array roots index⟩
  simp only [copyRoot, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    List.length_cons, List.length_nil] at body ⊢
  runBlock body

end ClAsm.Weigh
