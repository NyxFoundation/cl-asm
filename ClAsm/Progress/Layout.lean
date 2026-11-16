import ClAsm.Layout

namespace ClAsm.Progress

/-- Internal ABI record spans for the epoch-record rotation routine.  All
    constants are mainnet preset values at the pinned revision. -/
def slotsPerEpoch : Nat := ClAsm.Layout.slotsPerEpoch
/-- `EPOCHS_PER_HISTORICAL_VECTOR` -/
def epochsPerHistoricalVector : Nat := 65536
/-- `EPOCHS_PER_SLASHINGS_VECTOR` -/
def epochsPerSlashingsVector : Nat := 8192
/-- `EPOCHS_PER_ETH1_VOTING_PERIOD` -/
def epochsPerEth1VotingPeriod : Nat := 64

def entry : Nat := ClAsm.Layout.entry
def returnAddress : Nat := ClAsm.Layout.returnAddress

abbrev previousFlagsAddress : Nat := 0x70000000
abbrev currentFlagsAddress : Nat := 0x71000000
abbrev randaoMixesAddress : Nat := 0x72000000
abbrev slashingsAddress : Nat := 0x73000000
abbrev eth1CountAddress : Nat := 0x74000000

/-- Participation flags are zero-extended uint8 values in eight-byte words. -/
def flagBytes : Nat := 8
/-- One randao mix or slashing value per eight-byte word. -/
def mixBytes : Nat := 8

def randaoSpan : Nat := slashingsAddress - randaoMixesAddress
def slashingSpan : Nat := eth1CountAddress - slashingsAddress
/-- Fixed capacities bounded by the concrete image. -/
def randaoCapacity : Nat := randaoSpan / mixBytes
def slashingCapacity : Nat := slashingSpan / mixBytes
def flagCapacity : Nat := 0x100000 / flagBytes

theorem flag_span : flagCapacity = 131072 := by decide
theorem randao_span : randaoSpan = 0x1000000 := by decide
theorem slashing_span : slashingSpan = 0x1000000 := by decide
theorem randao_capacity_ge : epochsPerHistoricalVector ≤ randaoCapacity := by decide
theorem slashing_capacity_ge : epochsPerSlashingsVector ≤ slashingCapacity := by decide

theorem regions_aligned :
    previousFlagsAddress % 8 = 0 ∧ currentFlagsAddress % 8 = 0 ∧
    randaoMixesAddress % 8 = 0 ∧ slashingsAddress % 8 = 0 ∧ eth1CountAddress % 8 = 0 ∧
    entry % 4 = 0 ∧ returnAddress % 4 = 0 := by decide

theorem regions_disjoint :
    previousFlagsAddress + 0x100000 ≤ currentFlagsAddress ∧
    previousFlagsAddress + 0x100000 ≤ randaoMixesAddress ∧
    currentFlagsAddress + 0x100000 ≤ randaoMixesAddress ∧
    randaoMixesAddress + randaoSpan ≤ slashingsAddress ∧
    slashingsAddress + slashingSpan ≤ eth1CountAddress := by decide

end ClAsm.Progress
