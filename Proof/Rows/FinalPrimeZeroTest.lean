import Proof.Rows.FinalPrimeModularSum

/-! # The row verdict: testing a residue word for zero

Two consumers need it.  A threshold row of Appendix A.13 accepts a prime
exactly when the equation difference vanishes modulo that prime, i.e. when the
accumulated residue word is zero; and a trial division declares `d` a divisor
of `n` exactly when the residue word of `n mod d` is zero.

`machine : Machine 2 5` scans one framed word left to right, keeps an
"a one has been seen" bit in its finite control, and writes the verdict into
the one-cell result tape.  `2 * L + 1` steps, no head reset, two tapes.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeZeroTest
open LocalBitMultitape RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true



/-! ## 1. Local transitions -/

/-! ## 2. The sweep -/

def orAll : Bool → List Bool → Bool
  | f, [] => f
  | f, b :: bs => orAll (f || b) bs

/-! ## 3. Exact semantics -/

theorem orAll_false (f : Bool) (ws : List Bool) :
    orAll f ws = false ↔ f = false ∧ value ws = 0 := by
  induction ws generalizing f with
  | nil => simp [orAll, value]
  | cons b ws ih =>
    rw [orAll, ih (f || b)]
    cases f <;> cases b <;> simp [value]

theorem orAll_value (ws : List Bool) : (!orAll false ws) = decide (value ws = 0) := by
  cases h : orAll false ws
  · have := (orAll_false false ws).mp h
    simp [this.2]
  · have hne : ¬(value ws = 0) := by
      intro hz
      have := (orAll_false false ws).mpr ⟨rfl, hz⟩
      rw [h] at this
      exact Bool.noConfusion this
    simp [hne]

end NearCubicWires.RepairOrdinary.FinalPrimeZeroTest
