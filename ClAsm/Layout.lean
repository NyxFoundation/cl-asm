import RiscvZkvm.Rv64.Program

namespace ClAsm.Layout

def slotsPerEpoch : Nat := 32
def slotsPerHistoricalRoot : Nat := 8192
def stateBytes : Nat := 136
def rootBytes : Nat := 32
def rootsBytes : Nat := rootBytes * slotsPerHistoricalRoot
def scratchBytes : Nat := 80

/-- Executable code is outside the model's writable data windows. -/
def entry : Nat := 0x80000000
/-- The harness stops at this address before fetching another instruction. -/
def returnAddress : Nat := 0x80001000
def stateAddress : Nat := 0xa0000000
def rootsAddress : Nat := 0xa0010000
def scratchAddress : Nat := 0xa0050000

theorem regions_disjoint :
    stateAddress + stateBytes ≤ rootsAddress ∧
    rootsAddress + rootsBytes ≤ scratchAddress ∧
    scratchAddress + scratchBytes ≤ 0xc0000000 := by decide

theorem regions_aligned :
    stateAddress % 8 = 0 ∧ rootsAddress % 8 = 0 ∧ scratchAddress % 8 = 0 ∧
    entry % 4 = 0 ∧ returnAddress % 4 = 0 := by decide

end ClAsm.Layout
