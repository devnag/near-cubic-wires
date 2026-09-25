import Proof.Packets.CycleMaskWidth
import Proof.Packets.NormalizerData

/-! Concrete normalization arena: the record-width producer shares exactly
its W output with the normalizer. All normalizer scratch starts literally
empty, and the native serializer's index reserve is physically generated. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleNormalize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.ProjectionNormalization
open PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section



theorem dock_existing {t u : Nat} (slots : Fin t → Fin u)
    (H : Fin u → Nat) (h : Fin t → Nat) (hh : ∀ j,H (slots j)=h j) : dockH slots H h=H := by
  funext i
  unfold dockH
  cases hp : RecoveryFocus.pick slots i with
  | none => rfl
  | some j =>
    have hj := RecoveryFocus.slot_of_pick slots hp
    rw [←hj,hh j]

theorem dock_step {t u st fuel : Nat} {p : Machine t st}
    {h h' : Fin t → Nat} {A A' : Fin t → List Bool}
    (run : Step p fuel h A h' A') (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → Nat) (T : Fin u → List Bool)
    (hh : ∀ j,H (slots j)=h j) (ht : ∀ j,T (slots j)=A j) :
    Step (RecoveryFocus.machine slots p) fuel H T (dockH slots H h') (install slots T A') := by
  have r := run.focus slots hi H T
  rw [dock_existing slots H h hh,install_existing slots T A ht] at r
  exact r

end
end Theorem25Completion.CycleNormalize
