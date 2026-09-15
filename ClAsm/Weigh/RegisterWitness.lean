import ClAsm.Weigh.MemoryWitness

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

def registerHeap (regs : Reg → Option Word) : PartialState where
  regs := regs
  mem := fun _ => none
  pc := none

def registerCells (s : MachineState) (regs : List Reg) : Assertion :=
  match regs with
  | [] => empAssertion
  | r :: tail => (r ↦ᵣ s.getReg r) ** registerCells s tail

theorem registerCells_witness (s : MachineState) (regs : List Reg) (hn : regs.Nodup) :
    ∃ values, registerCells s regs (registerHeap values) ∧
      ∀ r v, values r = some v → r ∈ regs ∧ s.getReg r = v := by
  induction regs with
  | nil => exact ⟨fun _ => none, rfl, by simp⟩
  | cons r tail ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    obtain ⟨values, hv, hb⟩ := ih htail
    refine ⟨fun q => if q == r then some (s.getReg r) else values q, ?_, ?_⟩
    · refine ⟨PartialState.singletonReg r (s.getReg r), registerHeap values, ?_, ?_, rfl, hv⟩
      · refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
          Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
        intro q
        by_cases he : q = r
        · subst q
          right
          cases hq : values r with
          | none => exact hq
          | some v => exact False.elim (hnot (hb r v hq).1)
        · left; simp [PartialState.singletonReg, he]
      · simp [PartialState.union, PartialState.singletonReg, registerHeap]
        funext q
        by_cases h : q = r <;> simp [h]
    · intro q v hq
      dsimp only at hq
      split at hq
      · rename_i he
        have he' : q = r := by simpa using he
        subst q
        exact ⟨by simp, Option.some.inj hq⟩
      · have h := hb q v hq
        exact ⟨List.mem_cons_of_mem r h.1, h.2⟩

theorem registers_memory_compatible (s : MachineState) (regs : List Reg) (P : Assertion)
    (hn : regs.Nodup) (hm : ∀ a, s.getMem a = 0) {lo hi : Nat}
    (memory : MemoryWitness P lo hi) : (registerCells s regs ** P).holdsFor s := by
  obtain ⟨values, hv, hb⟩ := registerCells_witness s regs hn
  obtain ⟨mem, hp, bounds⟩ := memory
  have hd : (registerHeap values).Disjoint (memoryHeap mem) := by
    exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
      Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  refine ⟨(registerHeap values).union (memoryHeap mem), ?_,
    registerHeap values, memoryHeap mem, hd, rfl, hv, hp⟩
  rw [PartialState.CompatibleWith_union hd]
  constructor
  · exact ⟨fun r v h => (hb r v h).2, by simp [registerHeap], by simp [registerHeap],
      by simp [registerHeap], by simp [registerHeap], by simp [registerHeap], by simp [registerHeap]⟩
  · refine ⟨by simp [memoryHeap], ?_, by simp [memoryHeap], by simp [memoryHeap],
      by simp [memoryHeap], by simp [memoryHeap], by simp [memoryHeap]⟩
    intro a v h
    rw [hm, (bounds a v h).1]

end ClAsm.Weigh
