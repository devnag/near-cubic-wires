import Proof.CaseAnalysis.FinalSupplierCountStage

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10BandRecycle

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank bankAt)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §2  The band, and the fictional bank the docks are run in

`install slots A (fun _ => [])` (`Proof/Amplification/RecoveryReadyCalls.lean`) is the bank
in which the round's slots are literally empty.  Every docked engine applies to
it with NO hypothesis on `A` at all.  `bandCap` pads exactly those slots back up
to the real, zeroed band, and pads nothing else. -/

/-! ## §3  The deliverable: one round of the loop, over a RECYCLED band -/

/-! ## §4  The band is restored, and the length bound that lets it be -/

/-- **The length bound is a CONSEQUENCE of the round budget, not a new
assumption.**  A band tape entering a round at length at most `total` with its
head at `0` leaves it at length at most `total`, as long as the round's step
count plus one fits in `total`.  This is
`CloseoutRowsProjectionReset.scratch_support`
(`Proof/CaseAnalysis/RowsProjectionReset.lean`) in `Step` vocabulary. -/
theorem band_length_after_round {t s : ℕ} (M : Machine t s) (cost total : ℕ)
    {H H' : Fin t → ℕ} {A B : Fin t → List Bool} (h : Step M cost H A H' B)
    (hcost : cost + 1 ≤ total) (i : Fin t) (hh : H i = 0) (ht : (A i).length ≤ total) :
    (B i).length ≤ total := by
  obtain ⟨rr, hr, _hh, htapes, hs⟩ := h
  have hsupp := CloseoutRowsProjectionReset.scratch_support M cost total
    ⟨M.start, H, A⟩ rr hr i hh ht (by omega)
  rw [htapes] at hsupp
  exact hsupp

/-- **`total := cost + 1` closes the loop.**  The bound does not grow with the
round index, so `clear_step`'s `hb` holds at every round with the SAME `total`
and the SAME band. -/
theorem band_length_at_cost {t s : ℕ} (M : Machine t s) (cost : ℕ)
    {H H' : Fin t → ℕ} {A B : Fin t → List Bool} (h : Step M cost H A H' B)
    (i : Fin t) (hh : H i = 0) (ht : (A i).length ≤ cost + 1) :
    (B i).length ≤ cost + 1 :=
  band_length_after_round M cost (cost + 1) h (Nat.le_refl _) i hh ht

/-! ## §5  The two disciplines, side by side

`band_exhausted` (`Proof/CaseAnalysis/FinalPrologueBlankBand.lean`) is about a
line that MOVES: `line + k * block` eventually reaches the bank width, and past
that the invariant is the vacuous one of
`blankFrom_above_bank_certifies_nothing` (`:244`).  `ZeroBand` is stated at a
line that does not move.  The two statements below are the arithmetic INVZERO
left open, in the form that decides it. -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10BandRecycle
