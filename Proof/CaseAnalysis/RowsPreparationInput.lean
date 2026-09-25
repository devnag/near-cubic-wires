import Proof.CaseAnalysis.RowsPreparationFits

/-! The concrete shared preparation capacity discharges the actual native
metadata and every selected initial work-tape extent. The growing output
prefix is absent from all of these bounds. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPreparationInput
open CloseoutRowsPreparationBounds CloseoutRowsPreparationFits
open LocalBitMultitape CloseoutRowsLoopLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem small_fits (n p F w N Q : ℕ) :
    16*scale n p F w N Q ≤ capacity n p F w N Q := by
  have hS := (scale_fields n p F w N Q).1
  have hpow : scale n p F w N Q ≤ (scale n p F w N Q)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 4 by decide)
  have he : 1 ≤ 2^(w*(Q+1)) := Nat.one_le_two_pow
  unfold capacity
  nlinarith [Nat.mul_le_mul_right ((scale n p F w N Q)^4) he]

end NearCubicWires.RepairOrdinary.CloseoutRowsPreparationInput
