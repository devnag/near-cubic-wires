import Proof.CaseAnalysis.RowsEstimatorSubstitutionBounded
import Proof.Packets.CycleRawSingletonBudget
import Proof.Packets.PacketsXLiteralCache

/-! The original executed singleton-substitution consumer fits the common
physical reserve. All space and fuel premises are discharged from actual
reflected cache bytes, the width-policy degree bound, and raw row census. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleRawSingletonCost
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer
open CloseoutRowsRawPairSeek (Pair cacheWord)


theorem space_eq (cs : List Pair) (d : Nat) :
    CloseoutRowsEstimator.SubstitutionBounds.space cs 1 d (cacheWord cs).length=
      CycleRawSingletonBudget.space (cacheWord cs).length cs.length d := by
  simp only [CloseoutRowsEstimator.SubstitutionBounds.space,CloseoutRowsEstimator.SubstitutionBounds.capacity,CloseoutRowsEstimator.SubstitutionBounds.rowCapacity,CloseoutRowsEstimator.SubstitutionBounds.widthBound,
    CloseoutRowsEstimator.SubstitutionCache.capacity,CycleRawSingletonBudget.space,one_pow]
  ring
theorem fuel_eq (cs : List Pair) (d rows : Nat) :
    CloseoutRowsEstimator.SubstitutionBounds.fuel cs 1 d rows=
      CycleRawSingletonBudget.fuel (cacheWord cs).length cs.length d rows := by
  simp only [CloseoutRowsEstimator.SubstitutionBounds.fuel,space_eq,CycleRawSingletonBudget.fuel]

end Theorem25Completion.CycleRawSingletonCost
