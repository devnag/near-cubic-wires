import Proof.Hierarchy.CompetitorSelectedTableInput
import Proof.Hierarchy.CompetitorCountRecordRequestBounds

/-! Execute the actual natural count table and consume its output in place
in the request-derived six-field record caller. The row producer supplies
only its mask and coefficient/normalization fields, not the count stream. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open RepairRepresentation MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := CompetitorSelectedTable.tapes p+27
def slots (p : Program) : Fin 118 → Fin (tapes p) :=
  Fin.addCases (m := 91) (n := 27) (motive := fun _ => Fin (tapes p))
    (fun i => (CompetitorSelectedTable.slot p i).castAdd 27)
    (fun i => i.natAdd (CompetitorSelectedTable.tapes p))
noncomputable def first (a : WilliamsAlgorithm) :=
  TapeEmbedding.machine 27 (TapeEmbedding.machine 92 (CompetitorCountTable.machine a))
noncomputable def last (p : Program) := RecoveryFocus.machine (slots p) CompetitorCountRecordRequest.machine
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (first a) (last (producer a))
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) (Q : ℕ) :=
  CompetitorCountTable.budget a r Q+1+CompetitorCountRecordRequest.budget r Q

theorem slots_injective (p : Program) : Function.Injective (slots p) := by
  intro i j
  refine Fin.addCases (m := 91) (n := 27) ?_ ?_ i <;> intro x
  all_goals refine Fin.addCases (m := 91) (n := 27) ?_ ?_ j <;> intro y
  · intro h
    apply congrArg (fun z : Fin 91 => z.castAdd 27)
    apply CompetitorSelectedTable.slot_injective p
    have h' := congrArg Fin.val h
    simp only [slots,Fin.addCases_left,Fin.val_castAdd] at h'
    exact Fin.ext h'
  · intro h
    have h' := congrArg Fin.val h
    simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h'
    omega
  · intro h
    apply congrArg (fun z : Fin 27 => z.natAdd 91)
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [slots,Fin.addCases_right,Fin.val_natAdd] at h'
    omega

end NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
