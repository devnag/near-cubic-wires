import Proof.SourceAssembly.SourceSkelInitAll

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

theorem pad_long (Rc : Nat) (w : List Bool) : Rc ≤ (ZeroPadding.pad Rc w).length := by
  rw [ZeroPadding.pad_length]; exact le_max_left _ _

/-- Every strip slot of the whole init is `≥ Rc` long. -/
theorem slotVal_long (mode : Bool) (L q Rc DD CD Dcw Ccw CL DL i : Nat) :
    Rc ≤ (slotVal Rc (valAll mode L q Rc DD CD Dcw Ccw CL DL) i).length := by
  unfold slotVal valAll valR
  split_ifs <;> simp only [List.length_replicate, Rk] <;> first | exact pad_long _ _ | omega

end
end NearCubicWires.SourceSkeleton.InitS
end
