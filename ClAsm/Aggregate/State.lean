import ClAsm.Aggregate.Layout
import ClAsm.Arithmetic
import ClAsm.EpochAtSlot
import RiscvZkvm.Rv64.Logic.SepLogic
import Std.Tactic.BVDecide

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

/-- One registry entry in the routine's internal 32-byte layout:
    effective balance, activation epoch, exit epoch, slashed boolean, as words. -/
structure Validator where
  effectiveBalance : Word
  activationEpoch : Word
  exitEpoch : Word
  slashed : Word
  deriving Repr, BEq, DecidableEq

deriving instance Inhabited for Validator

instance : Inhabited (Validator × Word) := ⟨(default, 0)⟩

structure Input where
  slot : Word
  validators : List Validator
  previousFlags : List Word
  currentFlags : List Word
  deriving Repr, BEq, DecidableEq

def Validator.owns (base : Word) (validator : Validator) : Assertion :=
  (base + signExtend12 0 ↦ₘ validator.effectiveBalance) **
    (base + signExtend12 8 ↦ₘ validator.activationEpoch) **
    (base + signExtend12 16 ↦ₘ validator.exitEpoch) **
    (base + signExtend12 24 ↦ₘ validator.slashed)

/-- A word array stored as consecutive 8-byte cells. -/
def wordsOwn (base : Word) (words : List Word) : Assertion :=
  match words with
  | [] => empAssertion
  | word :: tail => (base ↦ₘ word) ** wordsOwn (base + BitVec.ofNat 64 8) tail

/-- The validator registry as consecutive 32-byte entries. -/
def validatorsOwn (base : Word) (validators : List Validator) : Assertion :=
  match validators with
  | [] => empAssertion
  | validator :: tail =>
      validator.owns base ** validatorsOwn (base + BitVec.ofNat 64 32) tail

theorem wordsOwn_pcFree (base : Word) (words : List Word) : (wordsOwn base words).pcFree := by
  induction words generalizing base with
  | nil => exact pcFree_emp
  | cons word tail ih =>
      exact pcFree_sepConj (by pcFree) (ih (base + BitVec.ofNat 64 8))

theorem validatorsOwn_pcFree (base : Word) (validators : List Validator) :
    (validatorsOwn base validators).pcFree := by
  induction validators generalizing base with
  | nil => exact pcFree_emp
  | cons validator tail ih =>
      exact pcFree_sepConj (by pcFree) (ih (base + BitVec.ofNat 64 32))

/-- Two immediate-offset words add without carrying. -/
theorem ofNat_add_le (m n : Nat) (h : m + n < 2^64) :
    BitVec.ofNat 64 m + BitVec.ofNat 64 n = BitVec.ofNat 64 (m + n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : m < 2^64),
    Nat.mod_eq_of_lt (by omega : n < 2^64),
    Nat.mod_eq_of_lt h]

/-- Adding a stride step to the routine's pointer arithmetic. -/
theorem stride_add (base : Word) (m n : Nat) (h : m + n < 2^64) :
    (base + BitVec.ofNat 64 m) + BitVec.ofNat 64 n = base + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.add_assoc, ofNat_add_le m n h]

theorem stride_succ_step (base : Word) (s k : Nat) (h : s * (k + 1) < 2^64) :
    (base + BitVec.ofNat 64 s) + BitVec.ofNat 64 (s * k) = base + BitVec.ofNat 64 (s * (k + 1)) := by
  have hs : s * (k + 1) = s + s * k := by simp [Nat.mul_add, Nat.mul_one, Nat.add_comm]
  rw [hs] at h
  have hb : s * (k + 1) < 2^64 := by rw [hs]; omega
  rw [BitVec.add_assoc, ofNat_add_le s (s * k) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : s + s * k < 2^64), Nat.mod_eq_of_lt hb]
  omega

/-- Split a word array at `index`: everything before stays at `base`, the rest
    is owned at the routine's pointer address. -/
theorem wordsOwn_take_drop (base : Word) (words : List Word) (index : Nat)
    (hbound : 8 * index < 2^64) :
    wordsOwn base words =
      (wordsOwn base (words.take index) **
        wordsOwn (base + BitVec.ofNat 64 (8 * index)) (words.drop index)) := by
  induction index generalizing base words with
  | zero => simp [wordsOwn, sepConj_emp_left']
  | succ k ih =>
      cases words with
      | nil => simp [wordsOwn, sepConj_emp_left']
      | cons word tail =>
          simp only [wordsOwn, List.take_succ_cons, List.drop_succ_cons]
          rw [ih (base + BitVec.ofNat 64 8) tail (by omega),
            stride_succ_step base 8 k (by omega), sepConj_assoc']

/-- Split a validator array at `index` the same way. -/
theorem validatorsOwn_take_drop (base : Word) (validators : List Validator) (index : Nat)
    (hbound : 32 * index < 2^64) :
    validatorsOwn base validators =
      (validatorsOwn base (validators.take index) **
        validatorsOwn (base + BitVec.ofNat 64 (32 * index)) (validators.drop index)) := by
  induction index generalizing base validators with
  | zero => simp [validatorsOwn, sepConj_emp_left']
  | succ k ih =>
      cases validators with
      | nil => simp [validatorsOwn, sepConj_emp_left']
      | cons validator tail =>
          simp only [validatorsOwn, List.take_succ_cons, List.drop_succ_cons]
          rw [ih (base + BitVec.ofNat 64 32) tail (by omega),
            stride_succ_step base 32 k (by omega), sepConj_assoc']

/-- Taking `k` prefix elements commutes with zipping. -/
theorem zip_take_take (validators : List Validator) (flags : List Word) (k : Nat) :
    (validators.zip flags).take k = (validators.take k).zip (flags.take k) := by
  induction validators generalizing k flags with
  | nil => cases flags <;> cases k <;> simp
  | cons validator vTail ih =>
      cases flags with
      | nil => cases k <;> simp
      | cons flag fTail =>
          cases k with
          | zero => simp
          | succ j => simp [List.take_succ_cons, ih fTail j]

/-- Zipping preserves indexed element access. -/
theorem zip_getElem (validators : List Validator) (flags : List Word) (k : Nat)
    (hk : k < validators.length) (hflags : k < flags.length) :
    (validators.zip flags)[k]! = (validators[k]!, flags[k]!) := by
  induction validators generalizing k flags with
  | nil => simp at hk
  | cons validator vTail ih =>
      cases flags with
      | nil => simp at hflags
      | cons flag fTail =>
          cases k with
          | zero => simp
          | succ j =>
              simp only [List.length_cons] at hk hflags
              have hj : j < vTail.length := by omega
              have hflagsj : j < fTail.length := by omega
              simp only [List.zip_cons_cons, List.getElem!_cons_succ]
              exact ih fTail j hj hflagsj

theorem zip_getElem_fst (validators : List Validator) (flags : List Word) (k : Nat)
    (h1 : k < validators.length) (h2 : k < flags.length) :
    ((validators.zip flags)[k]!).1 = validators[k]! :=
  congrArg Prod.fst (zip_getElem validators flags k h1 h2)

theorem zip_getElem_snd (validators : List Validator) (flags : List Word) (k : Nat)
    (h1 : k < validators.length) (h2 : k < flags.length) :
    ((validators.zip flags)[k]!).2 = flags[k]! :=
  congrArg Prod.snd (zip_getElem validators flags k h1 h2)

theorem zip_length (validators : List Validator) (flags : List Word) :
    (validators.zip flags).length = min validators.length flags.length := by
  induction validators generalizing flags with
  | nil => cases flags <;> simp
  | cons validator vTail ih =>
      cases flags with
      | nil => simp
      | cons flag fTail =>
          simp only [List.zip_cons_cons, List.length_cons, ih fTail, Nat.succ_min_succ]

/-- The pinned phase0 `EFFECTIVE_BALANCE_INCREMENT`. -/
def effectiveBalanceIncrement : Nat := 2^0 * 10^9

/-- The word the prologue materializes for the increment floor. -/
def incrementWord : Word := BitVec.ofNat 64 effectiveBalanceIncrement

/-- Reference `is_active_validator`, on word comparands. -/
def isActiveValidator (validator : Validator) (epoch : Word) : Bool :=
  !BitVec.ult epoch validator.activationEpoch && BitVec.ult epoch validator.exitEpoch

/-- Reference `has_flag(flags, TIMELY_TARGET_FLAG_INDEX)` for the 0b010 target bit. -/
def hasTargetFlag (flags : Word) : Bool := flags &&& 2 != 0

/-- An unslashed validator in the internal representation (uint8 boolean 0/1). -/
def isUnslashed (validator : Validator) : Bool := validator.slashed = 0

/-- The reference conjunction selecting a target contribution. -/
def contributesTarget (validator : Validator) (flags : Word) (epoch : Word) : Bool :=
  isActiveValidator validator epoch && hasTargetFlag flags && isUnslashed validator

def contributesActive (validator : Validator) (epoch : Word) : Bool :=
  isActiveValidator validator epoch

def contributionActive (validator : Validator) (epoch : Word) : Nat :=
  if contributesActive validator epoch then validator.effectiveBalance.toNat else 0

def contributionTarget (validator : Validator) (flags : Word) (epoch : Word) : Nat :=
  if contributesTarget validator flags epoch then validator.effectiveBalance.toNat else 0

/-- The pinned caller's active-balance accumulation. -/
def sumActive (validators : List Validator) (epoch : Word) : Nat :=
  match validators with
  | [] => 0
  | validator :: tail => contributionActive validator epoch + sumActive tail epoch

/-- The pinned caller's target-balance pair accumulation. -/
def sumTargetPairs (entries : List (Validator × Word)) (epoch : Word) : Nat :=
  match entries with
  | [] => 0
  | entry :: rest => contributionTarget entry.1 entry.2 epoch + sumTargetPairs rest epoch

/-- Target-balance accumulation over a validator registry and one flag array. -/
def sumTarget (validators : List Validator) (flags : List Word) (epoch : Word) : Nat :=
  sumTargetPairs (validators.zip flags) epoch

theorem sumTarget_eq (validators : List Validator) (flags : List Word) (epoch : Word) :
    sumTarget validators flags epoch = sumTargetPairs (validators.zip flags) epoch := rfl

theorem sumActive_take_succ (validators : List Validator) (epoch : Word) (k : Nat)
    (hlk : k < validators.length) :
    sumActive (validators.take (k + 1)) epoch =
      sumActive (validators.take k) epoch +
        contributionActive validators[k]! epoch := by
  induction validators generalizing k with
  | nil => simp at hlk
  | cons validator tail ih =>
      cases k with
      | zero => simp [sumActive, contributionActive]
      | succ j =>
          simp only [List.length_cons] at hlk
          have hj : j < tail.length := by omega
          simp only [List.take_succ_cons, sumActive]
          rw [ih j hj]
          simp only [List.getElem!_cons_succ]
          omega

theorem sumTargetPairs_take_succ (entries : List (Validator × Word)) (epoch : Word) (k : Nat)
    (hlk : k < entries.length) :
    sumTargetPairs (entries.take (k + 1)) epoch =
      sumTargetPairs (entries.take k) epoch +
        contributionTarget entries[k]!.1 entries[k]!.2 epoch := by
  induction entries generalizing k with
  | nil => simp at hlk
  | cons entry tail ih =>
      cases k with
      | zero => simp [sumTargetPairs, contributionTarget]
      | succ j =>
          simp only [List.length_cons] at hlk
          have hj : j < tail.length := by omega
          simp only [List.take_succ_cons, sumTargetPairs]
          rw [ih j hj]
          simp only [List.getElem!_cons_succ]
          omega

theorem sumTarget_take_succ (validators : List Validator) (flags : List Word) (epoch : Word)
    (k : Nat) (hlk : k < validators.length) (hflags : k < flags.length) :
    sumTarget (validators.take (k + 1)) (flags.take (k + 1)) epoch =
      (sumTarget (validators.take k) (flags.take k) epoch +
        contributionTarget validators[k]! flags[k]! epoch) := by
  have hz : k < (validators.zip flags).length := by
    rw [zip_length validators flags]
    omega
  rw [sumTarget_eq, sumTarget_eq, ← zip_take_take validators flags (k + 1),
    ← zip_take_take validators flags k,
    sumTargetPairs_take_succ _ _ k hz,
    zip_getElem_fst validators flags k hlk hflags,
    zip_getElem_snd validators flags k hlk hflags]

theorem sumActive_prefix_le (validators : List Validator) (epoch : Word) (k : Nat) :
    sumActive (validators.take k) epoch ≤ sumActive validators epoch := by
  induction validators generalizing k with
  | nil => cases k <;> simp [sumActive]
  | cons validator tail ih =>
      cases k with
      | zero => simp [sumActive, List.take_succ_cons]
      | succ j =>
          have le := ih j
          simp only [List.take_succ_cons, sumActive]
          omega

theorem sumTargetPairs_prefix_le (entries : List (Validator × Word)) (epoch : Word) (k : Nat) :
    sumTargetPairs (entries.take k) epoch ≤ sumTargetPairs entries epoch := by
  induction entries generalizing k with
  | nil => cases k <;> simp [sumTargetPairs]
  | cons entry tail ih =>
      cases k with
      | zero => simp [sumTargetPairs, List.take_succ_cons]
      | succ j =>
          have le := ih j
          simp only [List.take_succ_cons, sumTargetPairs]
          omega

theorem sumTarget_prefix_le (validators : List Validator) (flags : List Word) (epoch : Word)
    (k : Nat) :
    sumTarget (validators.take k) (flags.take k) epoch ≤ sumTarget validators flags epoch := by
  show sumTargetPairs ((validators.take k).zip (flags.take k)) epoch ≤
    sumTargetPairs (validators.zip flags) epoch
  rw [← zip_take_take validators flags k]
  exact sumTargetPairs_prefix_le (validators.zip flags) epoch k

def currentEpoch (input : Input) : Word := EpochAtSlot.epoch input.slot

/-- The word the machine computes for the caller's previous epoch. -/
def previousEpochWord (input : Input) : Word :=
  Arithmetic.previousValue (currentEpoch input)

/-- The pinned phase0 `get_total_balance` floor. -/
def saturateIncrement (sum : Nat) : Nat := Nat.max effectiveBalanceIncrement sum

/-- The routine's mathematical result: the three saturated balances. -/
def aggregateResult (input : Input) : Word × Word × Word :=
  let epoch := currentEpoch input
  (BitVec.ofNat 64 (saturateIncrement (sumActive input.validators epoch)),
    BitVec.ofNat 64 (saturateIncrement
      (sumTarget input.validators input.previousFlags (previousEpochWord input))),
    BitVec.ofNat 64 (saturateIncrement
      (sumTarget input.validators input.currentFlags epoch)))

theorem incrementWord_value : ((BitVec.ofNat 20 0x3B9AD).zeroExtend 32 <<< 12).signExtend 64 +
    signExtend12 0xA00 = incrementWord := by
  simp only [signExtend12, incrementWord, effectiveBalanceIncrement, Nat.reduceMul]
  bv_decide

end ClAsm.Aggregate
