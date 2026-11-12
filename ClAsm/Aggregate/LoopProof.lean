import ClAsm.Aggregate.Correctness

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

/-- An existentially quantified triple of temporary registers, framed by the
    rest of the loop invariant. -/
def tempInv (core : Assertion) : Assertion :=
  fun h => ∃ t5 t6 t7, (((.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7)) ** core) h

theorem drop_head (vs : List Validator) (i : Nat) (hi : i < vs.length) :
    vs.drop i = vs[i] :: vs.drop (i + 1) :=
  List.drop_eq_getElem_cons hi

theorem pointer_succ (base : Word) (s i : Nat) (h : base.toNat + s * (i + 1) < 2^64) :
    base + BitVec.ofNat 64 (s * i) + BitVec.ofNat 64 s =
      base + BitVec.ofNat 64 (s * (i + 1)) := by
  have hmul : s * (i + 1) = s * i + s := by rw [Nat.mul_add, Nat.mul_one]
  have hsi : s * i < 2^64 := by omega
  have hs : s < 2^64 := by omega
  have hmid : base.toNat + s * i < 2^64 := by omega
  apply BitVec.eq_of_toNat_eq
  have hpiece : s * i + s < 2^64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsi, Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt hmid, hmul, Nat.mod_eq_of_lt hpiece, Nat.add_assoc]

theorem owns_focus (base : Word) (vs : List Validator) (i : Nat)
    (hi : i < vs.length) (h32 : base.toNat + 32 * (i + 1) < 2^64) :
    validatorsOwn base vs =
      (validatorsOwn base (vs.take i) **
        (vs[i]).owns (base + BitVec.ofNat 64 (32 * i)) **
        validatorsOwn (base + BitVec.ofNat 64 (32 * (i + 1))) (vs.drop (i + 1))) := by
  rw [validatorsOwn_take_drop base vs i (by omega), drop_head vs i hi]
  simp only [validatorsOwn, pointer_succ base 32 i h32]

def loopFocus (ptr prevPtr currPtr counter epoch previous total prevAcc currAcc t5 t6 t7
    prevFlag currFlag : Word) (validator : Validator) : Assertion :=
  ((((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ total) **
        (.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) ** validator.owns ptr) **
      ((.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) **
        (.x31 ↦ᵣ previous) ** (.x29 ↦ᵣ prevAcc) ** (.x30 ↦ᵣ currAcc) **
        ((prevPtr + signExtend12 0) ↦ₘ prevFlag) ** ((currPtr + signExtend12 0) ↦ₘ currFlag))))

theorem mem_zero (ptr value : Word) : (ptr ↦ₘ value) = ((ptr + signExtend12 0) ↦ₘ value) := by
  rw [zeroSign]
  apply congrArg (fun address => address ↦ₘ value)
  exact (BitVec.add_zero (x := ptr)).symm

theorem step_focus (head ptr prevPtr currPtr counter epoch previous total prevAcc currAcc
    t5 t6 t7 prevFlag currFlag : Word) (validator : Validator) (tailOwn : Assertion)
    (htail : tailOwn.pcFree) (hneq : counter ≠ 0) :
    cpsTripleWithin 52 head head (CodeReq.ofProg head loop)
      (loopFocus ptr prevPtr currPtr counter epoch previous total prevAcc currAcc t5 t6 t7
        prevFlag currFlag validator ** tailOwn)
      ((((.x10 ↦ᵣ ptr + signExtend12 32) ** (.x11 ↦ᵣ prevPtr + signExtend12 8) **
            (.x12 ↦ᵣ currPtr + signExtend12 8) ** (.x13 ↦ᵣ counter + signExtend12 4095)) **
          (((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) **
              (.x30 ↦ᵣ foldedTarget currAcc epoch validator currFlag) **
              (.x5 ↦ᵣ targetBit epoch validator currFlag) **
              (.x6 ↦ᵣ selectedTarget epoch validator currFlag) **
              (.x7 ↦ᵣ targetMask epoch validator currFlag) ** validator.owns ptr **
              ((currPtr + signExtend12 0) ↦ₘ currFlag)) **
            ((.x31 ↦ᵣ previous) **
              (.x29 ↦ᵣ foldedTarget prevAcc previous validator prevFlag) **
              ((prevPtr + signExtend12 0) ↦ₘ prevFlag) **
              (.x17 ↦ᵣ foldedActive total epoch validator)))) **
        tailOwn) := by
  simpa [loopFocus] using
    cpsTripleWithin_frameR tailOwn htail
      (oneIteration head ptr prevPtr currPtr counter epoch previous total prevAcc currAcc
        t5 t6 t7 prevFlag currFlag validator hneq)

/-- What one iteration leaves untouched: the call-register frame, the ownership
    of the arrays past the current pointers, and the three scratch cells. -/
def tailFrame (ret slot scratch inc oldT oldP oldC : Word)
    (tailPtr tailPrevPtr tailCurrPtr : Word)
    (tail : List Validator) (tailFlags currFlags : List Word) : Assertion :=
  ((.x1 ↦ᵣ ret) ** (.x14 ↦ᵣ slot) ** (.x15 ↦ᵣ scratch) ** (.x28 ↦ᵣ inc) **
    validatorsOwn tailPtr tail ** wordsOwn tailPrevPtr tailFlags **
    wordsOwn tailCurrPtr currFlags ** ((scratch + signExtend12 0) ↦ₘ oldT) **
    ((scratch + signExtend12 8) ↦ₘ oldP) ** ((scratch + signExtend12 16) ↦ₘ oldC))

/-- The guard invariant core with explicit temps: `consumed` holds the sums of
    the processed prefix, `left` is owned at the pointers. -/
def guardCore (consumed : List Validator) (prevConsumed currConsumed : List Word)
    (left : List Validator) (prevLeft currLeft : List Word)
    (ptr prevPtr currPtr ret slot scratch inc oldT oldP oldC epoch previous : Word)
    (t5 t6 t7 : Word) : Assertion :=
  (((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) **
      (.x13 ↦ᵣ BitVec.ofNat 64 left.length) ** (.x16 ↦ᵣ epoch) ** (.x31 ↦ᵣ previous) **
      (.x17 ↦ᵣ BitVec.ofNat 64 (sumActive consumed epoch)) **
      (.x29 ↦ᵣ BitVec.ofNat 64 (sumTarget consumed prevConsumed previous)) **
      (.x30 ↦ᵣ BitVec.ofNat 64 (sumTarget consumed currConsumed epoch))) **
    (tailFrame ret slot scratch inc oldT oldP oldC ptr prevPtr currPtr left
      prevLeft currLeft)) ** ((.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7))

/-- The temps after one body iteration. -/
def bodyTemps (epoch : Word) (validator : Validator) (flags : Word) : Word × Word × Word :=
  (targetBit epoch validator flags, selectedTarget epoch validator flags,
    targetMask epoch validator flags)

/-- The temps after processing a prefix of the lists. -/
def lastTemps (epoch : Word) (start : Word × Word × Word) :
    List Validator → List Word → Word × Word × Word
  | [], _ => start
  | _, [] => start
  | validator :: vtail, flag :: ftail =>
      lastTemps epoch (bodyTemps epoch validator flag) vtail ftail


theorem eight_word : (8 : Word) = BitVec.ofNat 64 8 := by decide

theorem thirty_two_word : (32 : Word) = BitVec.ofNat 64 32 := by decide

theorem stride_eight (ptr : Word) : ptr + signExtend12 8 = ptr + BitVec.ofNat 64 8 := by
  rw [signEight, eight_word]

theorem stride_thirty_two (ptr : Word) : ptr + signExtend12 32 = ptr + BitVec.ofNat 64 32 := by
  rw [signThirtyTwo, thirty_two_word]

theorem ofNat_toNat_small (n : Nat) (h : n < 2^64) :
    (BitVec.ofNat 64 n : Word).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem addNat_toNat (base : Word) (k : Nat) (h : base.toNat + k < 2^64) :
    (base + BitVec.ofNat 64 k : Word) = BitVec.ofNat 64 (base.toNat + k) :=
  wordAdd base k h

theorem sumActive_append (validators : List Validator) (validator : Validator)
    (epoch : Word) :
    sumActive (validators ++ [validator]) epoch =
      sumActive validators epoch + contributionActive validator epoch := by
  induction validators with
  | nil => simp [sumActive, contributionActive, contributesActive]
  | cons head tail ih =>
      simp only [List.cons_append, sumActive, ih, Nat.add_assoc]

theorem zip_append_single (validators : List Validator) (flags : List Word)
    (validator : Validator) (flag : Word) (hlen : flags.length = validators.length) :
    (validators ++ [validator]).zip (flags ++ [flag]) =
      validators.zip flags ++ [(validator, flag)] := by
  induction validators generalizing flags with
  | nil => cases flags with
    | nil => simp
    | cons flagHead tailFlags => simp at hlen
  | cons head tail ih =>
      cases flags with
      | nil => simp at hlen
      | cons flagHead tailFlags =>
          have hlenTail : tailFlags.length = tail.length := by
            simp only [List.length_cons] at hlen
            omega
          simp only [List.zip_cons_cons, List.cons_append, ih tailFlags hlenTail]

theorem sumTargetPairs_append_single (entries : List (Validator × Word))
    (validator : Validator) (flag : Word) (epoch : Word) :
    sumTargetPairs (entries ++ [(validator, flag)]) epoch =
      sumTargetPairs entries epoch + contributionTarget validator flag epoch := by
  induction entries with
  | nil => simp [sumTargetPairs, contributionTarget, contributesTarget]
  | cons head tail ih =>
      simp only [List.cons_append, sumTargetPairs, ih, Nat.add_assoc]

theorem sumTarget_append_single (validators : List Validator) (flags : List Word)
    (validator : Validator) (flag : Word) (epoch : Word)
    (hlen : flags.length = validators.length) :
    sumTarget (validators ++ [validator]) (flags ++ [flag]) epoch =
      sumTarget validators flags epoch + contributionTarget validator flag epoch := by
  show sumTargetPairs ((validators ++ [validator]).zip (flags ++ [flag])) epoch = _
  rw [zip_append_single validators flags validator flag hlen, sumTargetPairs_append_single,
    sumTarget, ← sumTarget]

theorem sumTargetPairs_append (entries suffix : List (Validator × Word)) (epoch : Word) :
    sumTargetPairs (entries ++ suffix) epoch =
      sumTargetPairs entries epoch + sumTargetPairs suffix epoch := by
  induction entries with
  | nil => simp [sumTargetPairs]
  | cons head tail ih =>
      simp only [List.cons_append, sumTargetPairs, ih, Nat.add_assoc]

theorem zip_append (validators : List Validator) (suffixValidator : List Validator)
    (flags : List Word) (suffixFlags : List Word)
    (hflags : flags.length = validators.length)
    (_hsuffix : suffixFlags.length = suffixValidator.length) :
    (validators ++ suffixValidator).zip (flags ++ suffixFlags) =
      validators.zip flags ++ suffixValidator.zip suffixFlags := by
  induction validators generalizing flags with
  | nil =>
      cases flags with
      | nil => simp
      | cons flagHead tailFlags => simp at hflags
  | cons head tail ih =>
      cases flags with
      | nil => simp at hflags
      | cons flagHead tailFlags =>
          have hlenTail : tailFlags.length = tail.length := by
            simp only [List.length_cons] at hflags
            omega
          simp only [List.zip_cons_cons, List.cons_append, ih tailFlags hlenTail]

theorem sumActive_suffix_le (validators suffix : List Validator) (epoch : Word) :
    sumActive validators epoch ≤ sumActive (validators ++ suffix) epoch := by
  induction validators with
  | nil => simp [sumActive]
  | cons head tail ih =>
      simp only [List.cons_append, sumActive]
      omega

theorem sumTarget_suffix_le (validators : List Validator) (flags : List Word)
    (suffixValidator : List Validator) (suffixFlags : List Word) (epoch : Word)
    (hflags : flags.length = validators.length)
    (hsuffix : suffixFlags.length = suffixValidator.length) :
    sumTarget validators flags epoch ≤
      sumTarget (validators ++ suffixValidator) (flags ++ suffixFlags) epoch := by
  show sumTargetPairs (validators.zip flags) epoch ≤
    sumTargetPairs ((validators ++ suffixValidator).zip (flags ++ suffixFlags)) epoch
  rw [zip_append validators suffixValidator flags suffixFlags hflags hsuffix,
    sumTargetPairs_append]
  exact Nat.le_add_right _ _

def finalPtr (ptr : Word) (stride len : Nat) : Word :=
  ptr + BitVec.ofNat 64 (stride * len)

theorem tailFrame_pcFree (ret slot scratch inc oldT oldP oldC : Word)
    (tailPtr tailPrevPtr tailCurrPtr : Word)
    (tail : List Validator) (tailFlags tailFlagsTwo : List Word) :
    (tailFrame ret slot scratch inc oldT oldP oldC tailPtr tailPrevPtr tailCurrPtr tail
      tailFlags tailFlagsTwo).pcFree := by
  unfold tailFrame
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (by pcFree) ?_
  refine pcFree_sepConj (validatorsOwn_pcFree _ _) ?_
  refine pcFree_sepConj (wordsOwn_pcFree _ _) ?_
  refine pcFree_sepConj (wordsOwn_pcFree _ _) ?_
  exact pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (by pcFree))

-- The loop consumes the remaining validators: the guard processes the head of
-- `left`, accumulates the processed prefix sums, and exits through the guard's
-- second instruction; `F` is the caller-provided frame that must absorb the
-- consumed cells.
set_option maxHeartbeats 10000000 in
theorem loop_frame (head ptr prevPtr currPtr ret slot scratch inc oldT oldP oldC
    epoch previous t5 t6 t7 : Word)
    (consumed : List Validator) (prevConsumed currConsumed : List Word)
    (left : List Validator) (prevLeft currLeft : List Word)
    (hprevLen : prevLeft.length = left.length)
    (hcurrLen : currLeft.length = left.length)
    (hcprev : prevConsumed.length = consumed.length)
    (hccurr : currConsumed.length = consumed.length)
    (hptr : ptr.toNat + 32 * left.length < 2^64)
    (hprevAddr : prevPtr.toNat + 8 * left.length < 2^64)
    (hcurrAddr : currPtr.toNat + 8 * left.length < 2^64)
    (hslashed : ∀ v ∈ left, v.slashed = 0 ∨ v.slashed = 1)
    (hexitT : sumActive (consumed ++ left) epoch < 2^64)
    (hexitP : sumTarget (consumed ++ left) (prevConsumed ++ prevLeft) previous < 2^64)
    (hexitC : sumTarget (consumed ++ left) (currConsumed ++ currLeft) epoch < 2^64)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin (2 + 52 * left.length) head ((head + 4) + signExtend21 loopExitOffset)
      (CodeReq.ofProg head loop)
      (guardCore consumed prevConsumed currConsumed left prevLeft currLeft
        ptr prevPtr currPtr ret slot scratch inc oldT oldP oldC epoch previous t5 t6 t7 ** F)
      (guardCore (consumed ++ left) (prevConsumed ++ prevLeft) (currConsumed ++ currLeft)
        [] [] [] (finalPtr ptr 32 left.length) (finalPtr prevPtr 8 left.length)
        (finalPtr currPtr 8 left.length) ret slot scratch inc oldT oldP oldC epoch previous
        (lastTemps epoch (t5, t6, t7) left currLeft).1
        (lastTemps epoch (t5, t6, t7) left currLeft).2.1
        (lastTemps epoch (t5, t6, t7) left currLeft).2.2 **
        (validatorsOwn ptr left ** wordsOwn prevPtr prevLeft ** wordsOwn currPtr currLeft ** F)) := by
  induction left generalizing consumed prevConsumed currConsumed prevLeft currLeft
    ptr prevPtr currPtr t5 t6 t7 F with
  | nil =>
      cases prevLeft with
      | cons prevHead prevTail => simp at hprevLen
      | nil =>
          cases currLeft with
          | cons currHead currTail => simp at hcurrLen
          | nil =>
              simp only [List.append_nil, finalPtr, Nat.mul_zero, BitVec.add_zero,
                Nat.add_zero, lastTemps, List.length_nil, validatorsOwn, wordsOwn,
                sepConj_emp_left']
              have hconv : (guardCore consumed prevConsumed currConsumed [] [] []
                    ptr prevPtr currPtr ret slot scratch inc oldT oldP oldC epoch
                    previous t5 t6 t7 ** F) =
                  (((((.x13 ↦ᵣ BitVec.ofNat 64 ([] : List Validator).length) ** (.x0 ↦ᵣ 0)) **
                    (((.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) **
                        (.x16 ↦ᵣ epoch) ** (.x31 ↦ᵣ previous) **
                        (.x17 ↦ᵣ BitVec.ofNat 64 (sumActive consumed epoch)) **
                        (.x29 ↦ᵣ BitVec.ofNat 64 (sumTarget consumed prevConsumed previous)) **
                        (.x30 ↦ᵣ BitVec.ofNat 64 (sumTarget consumed currConsumed epoch)) **
                        (.x1 ↦ᵣ ret) ** (.x14 ↦ᵣ slot) ** (.x15 ↦ᵣ scratch) ** (.x28 ↦ᵣ inc) **
                        ((scratch + signExtend12 0) ↦ₘ oldT) **
                        ((scratch + signExtend12 8) ↦ₘ oldP) **
                        ((scratch + signExtend12 16) ↦ₘ oldC) **
                        (.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) ** F))))) := by
                unfold guardCore tailFrame
                simp only [validatorsOwn, wordsOwn, sepConj_emp_left']
                xperm
              rw [hconv] at ⊢
              have framed := cpsTripleWithin_frameR
                (((.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) **
                      (.x16 ↦ᵣ epoch) ** (.x31 ↦ᵣ previous) **
                      (.x17 ↦ᵣ BitVec.ofNat 64 (sumActive consumed epoch)) **
                      (.x29 ↦ᵣ BitVec.ofNat 64 (sumTarget consumed prevConsumed previous)) **
                      (.x30 ↦ᵣ BitVec.ofNat 64 (sumTarget consumed currConsumed epoch)) **
                      (.x1 ↦ᵣ ret) ** (.x14 ↦ᵣ slot) ** (.x15 ↦ᵣ scratch) ** (.x28 ↦ᵣ inc) **
                      ((scratch + signExtend12 0) ↦ₘ oldT) **
                      ((scratch + signExtend12 8) ↦ₘ oldP) **
                      ((scratch + signExtend12 16) ↦ₘ oldC) **
                      (.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) ** F))
                  (by exact (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hF))))))))))))))))))) (loop_empty head)
              exact framed
  | cons validator tail ih =>
      cases prevLeft with
      | nil => simp at hprevLen
      | cons prevFlag prevTail =>
          cases currLeft with
          | nil => simp at hcurrLen
          | cons currFlag currTail =>
              simp only [List.length_cons] at hptr hprevAddr hcurrAddr hprevLen hcurrLen
              have hprevTailLen : prevTail.length = tail.length := by omega
              have hcurrTailLen : currTail.length = tail.length := by omega
              have hlt : tail.length + 1 < 2^64 := by omega
              have hslashedHead : validator.slashed = 0 ∨ validator.slashed = 1 :=
                hslashed validator (by simp)
              have hslashedTail : ∀ v ∈ tail, v.slashed = 0 ∨ v.slashed = 1 :=
                fun v hv => hslashed v (List.mem_cons_of_mem _ hv)
              have hsumT : sumActive consumed epoch < 2^64 :=
                Nat.lt_of_le_of_lt (sumActive_suffix_le consumed (validator :: tail) epoch)
                  hexitT
              have hsumP : sumTarget consumed prevConsumed previous < 2^64 :=
                Nat.lt_of_le_of_lt
                  (sumTarget_suffix_le consumed prevConsumed (validator :: tail)
                    (prevFlag :: prevTail) previous (by omega)
                    (by simp [hprevTailLen])) hexitP
              have hsumC : sumTarget consumed currConsumed epoch < 2^64 :=
                Nat.lt_of_le_of_lt
                  (sumTarget_suffix_le consumed currConsumed (validator :: tail)
                    (currFlag :: currTail) epoch (by omega)
                    (by simp [hcurrTailLen])) hexitC
              have hsplitActive : (consumed ++ [validator]) ++ tail =
                  consumed ++ (validator :: tail) := by
                simp [List.append_assoc, List.nil_append]
              have hsplitPrev : (prevConsumed ++ [prevFlag]) ++ prevTail =
                  prevConsumed ++ (prevFlag :: prevTail) := by
                simp [List.append_assoc, List.nil_append]
              have hsplitCurr : (currConsumed ++ [currFlag]) ++ currTail =
                  currConsumed ++ (currFlag :: currTail) := by
                simp [List.append_assoc, List.nil_append]
              have hboundT :
                  (BitVec.ofNat 64 (sumActive consumed epoch)).toNat +
                    contributionActive validator epoch < 2^64 := by
                rw [ofNat_toNat_small _ hsumT]
                have hnext : sumActive (consumed ++ [validator]) epoch =
                    sumActive consumed epoch + contributionActive validator epoch :=
                  sumActive_append consumed validator epoch
                have hpref : sumActive (consumed ++ [validator]) epoch ≤
                    sumActive (consumed ++ (validator :: tail)) epoch := by
                  rw [← hsplitActive]
                  exact sumActive_suffix_le (consumed ++ [validator]) tail epoch
                omega
              have hboundP : sumTarget consumed prevConsumed previous +
                  contributionTarget validator prevFlag previous < 2^64 := by
                have hnext : sumTarget (consumed ++ [validator])
                    (prevConsumed ++ [prevFlag]) previous =
                  sumTarget consumed prevConsumed previous +
                    contributionTarget validator prevFlag previous :=
                  sumTarget_append_single consumed prevConsumed validator prevFlag previous
                    hcprev
                have hpref : sumTarget (consumed ++ [validator])
                    (prevConsumed ++ [prevFlag]) previous ≤
                    sumTarget (consumed ++ (validator :: tail))
                      (prevConsumed ++ (prevFlag :: prevTail)) previous := by
                  rw [← hsplitActive, ← hsplitPrev]
                  exact sumTarget_suffix_le (consumed ++ [validator])
                    (prevConsumed ++ [prevFlag]) tail prevTail previous
                    (by simp [hcprev]) (by simp [hprevTailLen])
                omega
              have hboundC : sumTarget consumed currConsumed epoch +
                  contributionTarget validator currFlag epoch < 2^64 := by
                have hnext : sumTarget (consumed ++ [validator])
                    (currConsumed ++ [currFlag]) epoch =
                  sumTarget consumed currConsumed epoch +
                    contributionTarget validator currFlag epoch :=
                  sumTarget_append_single consumed currConsumed validator currFlag epoch
                    hccurr
                have hpref : sumTarget (consumed ++ [validator])
                    (currConsumed ++ [currFlag]) epoch ≤
                    sumTarget (consumed ++ (validator :: tail))
                      (currConsumed ++ (currFlag :: currTail)) epoch := by
                  rw [← hsplitActive, ← hsplitCurr]
                  exact sumTarget_suffix_le (consumed ++ [validator])
                    (currConsumed ++ [currFlag]) tail currTail epoch
                    (by simp [hccurr]) (by simp [hcurrTailLen])
                omega
              let consAtoms : Assertion :=
                validator.owns ptr ** ((prevPtr + signExtend12 0) ↦ₘ prevFlag) **
                  ((currPtr + signExtend12 0) ↦ₘ currFlag)
              have hstep := step_focus head ptr prevPtr currPtr
                (BitVec.ofNat 64 (tail.length + 1)) epoch previous
                (BitVec.ofNat 64 (sumActive consumed epoch))
                (BitVec.ofNat 64 (sumTarget consumed prevConsumed previous))
                (BitVec.ofNat 64 (sumTarget consumed currConsumed epoch))
                t5 t6 t7 prevFlag currFlag validator
                (tailFrame ret slot scratch inc oldT oldP oldC (ptr + BitVec.ofNat 64 32)
                  (prevPtr + BitVec.ofNat 64 8) (currPtr + BitVec.ofNat 64 8) tail
                  prevTail currTail) (tailFrame_pcFree ret slot scratch inc oldT oldP oldC
                    (ptr + BitVec.ofNat 64 32) (prevPtr + BitVec.ofNat 64 8)
                    (currPtr + BitVec.ofNat 64 8) tail prevTail currTail)
                (counter_succ_ne tail.length hlt)
              have hentryEq : (loopFocus ptr prevPtr currPtr (BitVec.ofNat 64 (tail.length + 1))
                  epoch previous (BitVec.ofNat 64 (sumActive consumed epoch))
                  (BitVec.ofNat 64 (sumTarget consumed prevConsumed previous))
                  (BitVec.ofNat 64 (sumTarget consumed currConsumed epoch)) t5 t6 t7
                  prevFlag currFlag validator **
                tailFrame ret slot scratch inc oldT oldP oldC (ptr + BitVec.ofNat 64 32)
                  (prevPtr + BitVec.ofNat 64 8) (currPtr + BitVec.ofNat 64 8) tail
                  prevTail currTail ** F) =
                (guardCore consumed prevConsumed currConsumed
                  (validator :: tail) (prevFlag :: prevTail) (currFlag :: currTail)
                  ptr prevPtr currPtr ret slot scratch inc oldT oldP oldC epoch
                  previous t5 t6 t7 ** F) := by
                simp only [guardCore, tailFrame, loopFocus, validatorsOwn, wordsOwn,
                  List.length_cons]
                rw [mem_zero prevPtr prevFlag, mem_zero currPtr currFlag]
                xperm
              have hframed := cpsTripleWithin_frameR F hF hstep
              rw [sepConj_assoc', hentryEq] at hframed
              have hstep2 : cpsTripleWithin 52 head head (CodeReq.ofProg head loop)
                  (guardCore consumed prevConsumed currConsumed
                    (validator :: tail) (prevFlag :: prevTail) (currFlag :: currTail)
                    ptr prevPtr currPtr ret slot scratch inc oldT oldP oldC epoch
                    previous t5 t6 t7 ** F)
                  (guardCore (consumed ++ [validator]) (prevConsumed ++ [prevFlag])
                    (currConsumed ++ [currFlag]) tail prevTail currTail
                    (ptr + BitVec.ofNat 64 32) (prevPtr + BitVec.ofNat 64 8)
                    (currPtr + BitVec.ofNat 64 8) ret slot scratch inc oldT oldP oldC
                    epoch previous (bodyTemps epoch validator currFlag).1
                    (bodyTemps epoch validator currFlag).2.1
                    (bodyTemps epoch validator currFlag).2.2 ** (consAtoms ** F)) := by
                refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hframed
                intro h hp
                have hfoldT := foldedActive_spec
                  (BitVec.ofNat 64 (sumActive consumed epoch)) epoch validator hboundT
                have hfoldP := foldedTarget_spec
                  (BitVec.ofNat 64 (sumTarget consumed prevConsumed previous)) previous
                  validator prevFlag hslashedHead (by
                    rw [ofNat_toNat_small _ hsumP]; exact hboundP)
                have hfoldC := foldedTarget_spec
                  (BitVec.ofNat 64 (sumTarget consumed currConsumed epoch)) epoch
                  validator currFlag hslashedHead (by
                    rw [ofNat_toNat_small _ hsumC]; exact hboundC)
                rw [ofNat_toNat_small _ hsumT] at hfoldT
                rw [ofNat_toNat_small _ hsumP] at hfoldP
                rw [ofNat_toNat_small _ hsumC] at hfoldC
                rw [hfoldT, hfoldP, hfoldC, stride_thirty_two, stride_eight,
                  stride_eight, counter_dec tail.length hlt] at hp
                refine Eq.mp ?_ hp
                apply congrArg (fun p : Assertion => p h)
                change _ = (guardCore (consumed ++ [validator]) (prevConsumed ++ [prevFlag])
                  (currConsumed ++ [currFlag]) tail prevTail currTail
                  (ptr + BitVec.ofNat 64 32) (prevPtr + BitVec.ofNat 64 8)
                  (currPtr + BitVec.ofNat 64 8) ret slot scratch inc oldT oldP oldC
                  epoch previous (bodyTemps epoch validator currFlag).1
                  (bodyTemps epoch validator currFlag).2.1
                  (bodyTemps epoch validator currFlag).2.2 ** (consAtoms ** F))
                simp only [guardCore, bodyTemps, consAtoms,
                  sumActive_append, sumTarget_append_single _ _ _ _ _ hcprev,
                  sumTarget_append_single _ _ _ _ _ hccurr]
                xperm
              have hptr32 : (ptr + BitVec.ofNat 64 32).toNat + 32 * tail.length < 2^64 := by
                rw [wordAdd ptr 32 (by omega), ofNat_toNat_small _ (by omega)]
                omega
              have hprev8 : (prevPtr + BitVec.ofNat 64 8).toNat + 8 * tail.length < 2^64 := by
                rw [wordAdd prevPtr 8 (by omega), ofNat_toNat_small _ (by omega)]
                omega
              have hcurr8 : (currPtr + BitVec.ofNat 64 8).toNat + 8 * tail.length < 2^64 := by
                rw [wordAdd currPtr 8 (by omega), ofNat_toNat_small _ (by omega)]
                omega
              have hih := ih (ptr := ptr + BitVec.ofNat 64 32)
                (prevPtr := prevPtr + BitVec.ofNat 64 8)
                (currPtr := currPtr + BitVec.ofNat 64 8)
                (consumed := consumed ++ [validator])
                (prevConsumed := prevConsumed ++ [prevFlag])
                (currConsumed := currConsumed ++ [currFlag])
                (t5 := (bodyTemps epoch validator currFlag).1)
                (t6 := (bodyTemps epoch validator currFlag).2.1)
                (t7 := (bodyTemps epoch validator currFlag).2.2)
                prevTail currTail hprevTailLen hcurrTailLen
                (by simp [hcprev]) (by simp [hccurr]) hptr32 hprev8 hcurr8 hslashedTail
                (by simpa only [hsplitActive] using hexitT)
                (by simpa only [hsplitActive, hsplitPrev] using hexitP)
                (by simpa only [hsplitActive, hsplitCurr] using hexitC)
                (consAtoms ** F) (pcFree_sepConj (by unfold consAtoms; pcFree) hF)
              have composed := cpsTripleWithin_seq_same_cr hstep2 hih
              have hfinal32 : finalPtr (ptr + BitVec.ofNat 64 32) 32 tail.length =
                  finalPtr ptr 32 (validator :: tail).length := by
                exact stride_succ_step ptr 32 tail.length (by omega)
              have hfinalPrev : finalPtr (prevPtr + BitVec.ofNat 64 8) 8 tail.length =
                  finalPtr prevPtr 8 (validator :: tail).length := by
                exact stride_succ_step prevPtr 8 tail.length (by omega)
              have hfinalCurr : finalPtr (currPtr + BitVec.ofNat 64 8) 8 tail.length =
                  finalPtr currPtr 8 (validator :: tail).length := by
                exact stride_succ_step currPtr 8 tail.length (by omega)
              rw [hsplitActive, hsplitPrev, hsplitCurr, hfinal32, hfinalPrev,
                hfinalCurr] at composed
              have hcount : 52 + (2 + 52 * tail.length) =
                  2 + 52 * (validator :: tail).length := by simp; omega
              rw [hcount] at composed
              refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ composed
              intro h hp
              simp only [lastTemps, validatorsOwn, wordsOwn]
              rw [mem_zero prevPtr prevFlag, mem_zero currPtr currFlag]
              unfold consAtoms at hp
              refine Eq.mp ?_ hp
              apply congrArg (fun p : Assertion => p h)
              xperm

end ClAsm.Aggregate
