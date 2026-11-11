import ClAsm.Layout

namespace ClAsm.Aggregate

/-- Each validator occupies four little-endian 64-bit words in SSZ field order:
    effective balance, activation epoch, exit epoch, and the slashed boolean. -/
def validatorBytes : Nat := 32
/-- Each participation entry is one zero-extended uint8 stored in one word. -/
def flagBytes : Nat := 8
/-- The routine writes total active, previous target, and current target balances. -/
def answerBytes : Nat := 24

def entry : Nat := ClAsm.Layout.entry
def returnAddress : Nat := ClAsm.Layout.returnAddress

def validatorsAddress : Nat := 0xa0000000
def previousFlagsAddress : Nat := 0xa0100000
def currentFlagsAddress : Nat := 0xa0200000
def scratchAddress : Nat := 0xa0300000

/-- Region spans the concrete image admits before reaching the next region. -/
def validatorSpan : Nat := previousFlagsAddress - validatorsAddress
def flagSpan : Nat := currentFlagsAddress - previousFlagsAddress
def answerSpan : Nat := 0x100000
/-- The concrete layout bounds the admitted validator count. -/
def capacity : Nat := min (validatorSpan / validatorBytes) (flagSpan / flagBytes)

theorem validators_span : validatorSpan = 0x100000 := by decide
theorem flag_span : flagSpan = 0x100000 := by decide
theorem capacity_eq : capacity = 32768 := by decide

theorem regions_aligned :
    validatorsAddress % 8 = 0 ∧ previousFlagsAddress % 8 = 0 ∧
    currentFlagsAddress % 8 = 0 ∧ scratchAddress % 8 = 0 ∧
    entry % 4 = 0 ∧ returnAddress % 4 = 0 := by decide

theorem regions_disjoint :
    validatorsAddress + validatorSpan ≤ previousFlagsAddress ∧
    previousFlagsAddress + flagSpan ≤ currentFlagsAddress ∧
    currentFlagsAddress + 0x100000 ≤ scratchAddress ∧
    scratchAddress + answerBytes ≤ 0xc0000000 := by decide

end ClAsm.Aggregate
