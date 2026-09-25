import Proof.CaseAnalysis.RowsPreparationBounds

/-! One concrete preparation capacity covers every degree of every
polynomial whose monomial count fits the shared digit width. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPreparationFits
open CloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scale_fields (n p F w N Q : ℕ) :
    1 ≤ scale n p F w N Q ∧ n ≤ scale n p F w N Q ∧ p ≤ scale n p F w N Q ∧
      F ≤ scale n p F w N Q ∧ w ≤ scale n p F w N Q ∧ N ≤ scale n p F w N Q ∧
      Q+1 ≤ scale n p F w N Q := by unfold scale; omega

end NearCubicWires.RepairOrdinary.CloseoutRowsPreparationFits
