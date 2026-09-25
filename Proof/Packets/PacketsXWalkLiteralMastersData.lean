import Proof.Packets.PacketsXVectorLiteralPalettePadding

/-! Paid palette master construction from raw numeric words and the actual mask.
Every derived scalar, template, padding cell and zero seed word is produced by execution. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralMasters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Completion
noncomputable section
def input (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) : List Bool :=
  if i=0 then List.replicate C true else if i=1 then List.replicate R true else
  if i=2 then List.replicate root true else if i=3 then List.replicate rank true else
  if i=4 then List.replicate depth true else if i=5 then List.replicate M true else
  if i=6 then mask else []

def affineOutput (n c d : Nat) := Classical.choose (UnaryAffine.run n c d)
theorem affine_step (n c d : Nat) : Step (UnaryAffine.machine c d) (UnaryAffine.budget n c d)
    (fun _=>0) (UnaryAffine.input n) (fun _=>0) (affineOutput n c d) :=
  (Classical.choose_spec (UnaryAffine.run n c d)).1
theorem affine_source (n c d : Nat) : affineOutput n c d 0=List.replicate n true :=
  (Classical.choose_spec (UnaryAffine.run n c d)).2.1
theorem affine_value (n c d : Nat) : affineOutput n c d 9=List.replicate (c*n+d) true :=
  (Classical.choose_spec (UnaryAffine.run n c d)).2.2

theorem zero_heads {t : Nat} (slots : Fin t→Fin 55) :
    dockH slots (fun _ : Fin 55=>0) (fun _=>0)=(fun _=>0) := by
  funext i
  unfold dockH
  cases RecoveryFocus.pick slots i <;>rfl
end
end Theorem25Completion.WalkLiteralMasters
