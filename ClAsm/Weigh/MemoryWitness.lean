import ClAsm.Weigh.Contract

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

def memoryHeap (mem : Word → Option Word) : PartialState where
  regs := fun _ => none
  mem := mem
  pc := none

/-- A zero-valued memory resource with a proved finite address range. -/
def MemoryWitness (P : Assertion) (lo hi : Nat) : Prop :=
  ∃ mem, P (memoryHeap mem) ∧
    ∀ a v, mem a = some v → v = 0 ∧ lo ≤ a.toNat ∧ a.toNat < hi

theorem memoryWitness_widen {P : Assertion} {lo hi lo' hi' : Nat}
    (h : MemoryWitness P lo hi) (hl : lo' ≤ lo) (hh : hi ≤ hi') : MemoryWitness P lo' hi' := by
  obtain ⟨mem, hp, hb⟩ := h
  refine ⟨mem, hp, ?_⟩
  intro a v hv
  have h := hb a v hv
  exact ⟨h.1, Nat.le_trans hl h.2.1, Nat.lt_of_lt_of_le h.2.2 hh⟩

theorem memoryWitness_sep {P Q : Assertion} {lo mid hi : Nat}
    (hp : MemoryWitness P lo mid) (hq : MemoryWitness Q mid hi)
    (hl : lo ≤ mid) (hh : mid ≤ hi) : MemoryWitness (P ** Q) lo hi := by
  obtain ⟨pm, hp, bp⟩ := hp
  obtain ⟨qm, hq, bq⟩ := hq
  refine ⟨fun a => (pm a).or (qm a), ?_, ?_⟩
  · refine ⟨memoryHeap pm, memoryHeap qm, ?_, ?_, hp, hq⟩
    · simp only [PartialState.Disjoint, memoryHeap, true_or, and_true]
      refine ⟨fun _ => trivial, ?_, fun _ => trivial⟩
      intro a
      cases ep : pm a with
      | none => exact Or.inl rfl
      | some v =>
        right
        cases eq : qm a with
        | none => rfl
        | some w => have := bp a v ep; have := bq a w eq; omega
    · simp [PartialState.union, memoryHeap, Option.or]
      funext a
      cases pm a <;> rfl
  · intro a v hv
    dsimp only at hv
    cases ep : pm a with
    | none =>
      have := bq a v (by simpa [ep] using hv)
      exact ⟨this.1, Nat.le_trans hl this.2.1, this.2.2⟩
    | some w =>
      have he : w = v := by simpa [ep] using hv
      subst he
      have := bp a w ep
      exact ⟨this.1, this.2.1, Nat.lt_of_lt_of_le this.2.2 hh⟩

def zeroCells (start count : Nat) : Assertion :=
  match count with
  | 0 => empAssertion
  | n + 1 => (BitVec.ofNat 64 start ↦ₘ 0) ** zeroCells (start + 8) n

theorem memoryWitness_cell (start : Nat) (halign : start % 8 = 0)
    (hlo : RAM_MEM_START ≤ start) (hhi : start + 8 ≤ RAM_MEM_END) :
    MemoryWitness (BitVec.ofNat 64 start ↦ₘ 0) start (start + 8) := by
  have hbound : start < 2^64 := by unfold RAM_MEM_END at hhi; omega
  have ha : (BitVec.ofNat 64 start).toNat = start := Nat.mod_eq_of_lt hbound
  refine ⟨fun a => if a == BitVec.ofNat 64 start then some 0 else none, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    simp [isValidDwordAccess, isValidMemAddr, isAligned8, ha, halign, hlo,
      show start ≤ RAM_MEM_END by omega]
  · intro a v hv
    dsimp only at hv
    split at hv
    · rename_i he
      have he' : a = BitVec.ofNat 64 start := by simpa using he
      subst a
      simp_all [Nat.mod_eq_of_lt hbound]
    · contradiction

theorem zeroCells_witness (start count : Nat) (halign : start % 8 = 0)
    (hlo : RAM_MEM_START ≤ start) (hhi : start + 8 * count ≤ RAM_MEM_END) :
    MemoryWitness (zeroCells start count) start (start + 8 * count) := by
  induction count generalizing start with
  | zero => exact ⟨fun _ => none, rfl, by simp⟩
  | succ n ih =>
    have hp := memoryWitness_cell start halign hlo (by omega)
    have hq := ih (start + 8) (by omega) (by omega) (by omega)
    have h := memoryWitness_sep hp hq (by omega) (by omega)
    simpa only [zeroCells, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

theorem zeroCells_append (start m n : Nat) :
    zeroCells start (m + n) = (zeroCells start m ** zeroCells (start + 8 * m) n) := by
  induction m generalizing start with
  | zero => simp [zeroCells, sepConj_emp_left']
  | succ m ih =>
    rw [Nat.succ_add, zeroCells, zeroCells, ih, sepConj_assoc']
    rw [show start + 8 + 8 * m = start + 8 * (m + 1) by omega]

def zeroRoot : Root := ⟨0, 0, 0, 0⟩
def zeroCheckpoint : Checkpoint := ⟨0, zeroRoot⟩

theorem zeroRoot_cells (start : Nat) : zeroRoot.owns (BitVec.ofNat 64 start) = zeroCells start 4 := by
  simp [zeroRoot, Root.owns, zeroCells, signExtend12, BitVec.ofNat_add, BitVec.add_assoc,
    sepConj_emp_right']

theorem zeroCheckpoint_cells (start : Nat) :
    zeroCheckpoint.owns (BitVec.ofNat 64 start) = zeroCells start 5 := by
  simp [zeroCheckpoint, zeroRoot, Checkpoint.owns, zeroCells, signExtend12,
    BitVec.ofNat_add, BitVec.add_assoc, sepConj_emp_right']

theorem rootsOwn_zero_cells (start count : Nat) :
    rootsOwn (BitVec.ofNat 64 start) (List.replicate count zeroRoot) = zeroCells start (4 * count) := by
  induction count generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, rootsOwn, zeroRoot_cells]
    rw [show BitVec.ofNat 64 start + 32 = BitVec.ofNat 64 (start + 32) by
      rw [BitVec.ofNat_add]; rfl]
    rw [ih, show 4 * (n + 1) = 4 + 4 * n by omega, zeroCells_append]

end ClAsm.Weigh
