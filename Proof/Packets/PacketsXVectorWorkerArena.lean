import Proof.Packets.GradedWindowReusable
import Proof.Packets.PacketsXDeltaMetadata

/-! Concrete 296-tape numeric arena. All window and delta scalar masters are
outside the private arithmetic work, and the cleanup is an actual parallel
R-cell overwrite with retained capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open RecoveryRootRound
noncomputable section

def heads (i : Fin 296) : Nat :=
  if i=31 ∨ i=258 ∨ i=259 ∨ i=260 then 1 else 0
def windowSlots : Fin 13→Fin 296 := ![264,266,267,268,295,32,260,269,270,152,271,151,31]
def windowMachine := RecoveryFocus.machine windowSlots GradedWindow.reusable

theorem window_run (R root level old : Nat) (A : Fin 296→List Bool)
    (hin : ∀j,A (windowSlots j)=GradedWindow.A R root level 0 0 old j)
    (hroot : root+67≤R) (hlevel : level+2≤R) (hold : old+1≤R) :
    Step windowMachine (2*R+3+GradedWindow.budget R root level) heads A heads
      (Function.update A 152 (ZeroPadding.pad R (CompareMachine.word (GradedWindow.window root level)))) := by
  apply PhysicalFocusBoundary.focus (GradedWindow.reusable_run R root level old hroot hlevel hold)
    windowSlots (by decide) heads heads A _
  · intro j;fin_cases j <;>rfl
  · exact fun j=>(hin j).symm
  · intro j;fin_cases j <;>rfl
  · intro j
    fin_cases j <;> simp only [windowSlots,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    all_goals first
      | exact (hin _).symm
      | rfl
  · intro i away
    have hn : i≠152 := by intro he;exact away 9 he.symm
    exact ⟨rfl,by simp only [Function.update_of_ne hn]⟩

/-- Inputs n,W,parent,child,u are retained on150,152,259,258,183.
The outputs offset,twice-W,target are produced directly on180,181,182;
276 and279 hold the actual lower and upper validity bits. -/
def metadataSlots : Fin 25→Fin 296 :=
  ![150,152,259,258,183,264,265,266,267,268,269,180,181,270,271,272,273,274,275,276,277,182,278,279,280]
def metadataMachine := RecoveryFocus.machine metadataSlots DeltaMetadata.machine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
