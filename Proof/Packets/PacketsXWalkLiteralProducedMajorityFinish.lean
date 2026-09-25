import Proof.Packets.PacketsXWalkLiteralProducedMajorityColumn

/-! Initialize the majority arena around the physically extracted column,
then restore the actual visit driver's cursor for repeated column use. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open Theorem25Completion.CycleBounds
noncomputable section
attribute [local irreducible] MajorityComplete.Cold.square MajorityComplete.Cold.copy MajorityComplete.Cold.initializeMachine

def finishBudget (R : Nat) := MajorityComplete.Width.budget R+2+1+(2*R^2+4+1+(2*R^2+6))
def finishedHeads (H : Fin 742→Nat) := dockH coldSlots H MajorityComplete.Cold.resultHeads
def finishedBank (C R n : Nat) (ps : List (Ring.Poly Nat)) (A : Fin 742→List Bool) :=
  install coldSlots A (MajorityComplete.Cold.result C R n ps)
def readyHeads (H : Fin 742→Nat) := Function.update (finishedHeads H) 709 1

theorem finish_run (C w n : Nat) (ps : List (Ring.Poly Nat)) (hlen : ps.length=n+1)
    (hN : n+1≤2^w) (hCodes : 2^(n+1)≤2^w) (hw : 1≤w)
    (H : Fin 742→Nat) (A : Fin 742→List Bool) (hh : ∀j,H (coldSlots j)=0)
    (ha : ∀j,A (coldSlots j)=MajorityComplete.Cold.afterScalar C (commonReserve C w) n
      (OrderedPacketStep.bank C (commonReserve C w) ps) j) :
    Step majorityFinish (finishBudget (commonReserve C w)) H A (finishedHeads H)
      (finishedBank C (commonReserve C w) n ps A) := by
  have h:= (MajorityComplete.Cold.square_run C (commonReserve C w) n _).seq
    ((MajorityComplete.Cold.copy_run C w n _ hN hCodes hw).seq
      (MajorityComplete.Cold.initialize_run C w n ps hlen hN hCodes hw))
  exact SourceDock.dock h coldSlots cold_injective H A hh ha

theorem raise_time_run (H : Fin 742→Nat) (A : Fin 742→List Bool) :
    Step raiseTime 1 (finishedHeads H) A (readyHeads H) A := by
  have hp : finishedHeads H 709=0 :=
    (dockH_slot coldSlots cold_injective H MajorityComplete.Cold.resultHeads 146).trans
      MajorityComplete.Cold.result_count_head
  have h:=PhysicalIndexReload.move_run (709 : Fin 742) .right (finishedHeads H) A
  simpa only [hp,HeadMove.apply,Nat.zero_add,raiseTime,readyHeads] using h

def finishReady := Composition.machine majorityFinish raiseTime

theorem finish_ready_run (C w n : Nat) (ps : List (Ring.Poly Nat)) (hlen : ps.length=n+1)
    (hN : n+1≤2^w) (hCodes : 2^(n+1)≤2^w) (hw : 1≤w)
    (H : Fin 742→Nat) (A : Fin 742→List Bool) (hh : ∀j,H (coldSlots j)=0)
    (ha : ∀j,A (coldSlots j)=MajorityComplete.Cold.afterScalar C (commonReserve C w) n
      (OrderedPacketStep.bank C (commonReserve C w) ps) j) :
    Step finishReady (finishBudget (commonReserve C w)+2) H A (readyHeads H)
      (finishedBank C (commonReserve C w) n ps A) := by
  exact (finish_run C w n ps hlen hN hCodes hw H A hh ha).seq (raise_time_run H _)

theorem ready_majority_heads (H : Fin 742→Nat) (j : Fin 137) :
    readyHeads H (majoritySlots j)=MajorityComplete.Bootstrap.heads j := by
  have away : majoritySlots j≠709 := by
    intro he
    have hb:=(majority_range j).2
    have hv:=congrArg Fin.val he
    change (majoritySlots j).val=709 at hv
    omega
  rw [readyHeads,Function.update_of_ne away,←cold_majority,finishedHeads,
    dockH_slot coldSlots cold_injective,MajorityComplete.Cold.result_heads]

theorem ready_majority_words (C R n : Nat) (ps : List (Ring.Poly Nat)) (A : Fin 742→List Bool) (j : Fin 137) :
    finishedBank C R n ps A (majoritySlots j)=
      MajorityComplete.Bootstrap.readyWith (MajorityComplete.Cold.masters C R (n+1) (R^2)) C R (R^2) ps j := by
  rw [←cold_majority,finishedBank,install_slot coldSlots cold_injective,MajorityComplete.Cold.result_arena]

theorem ready_column_words (C R n : Nat) (ps : List (Ring.Poly Nat)) (A : Fin 742→List Bool)
    (col : Fin 9→List Bool) (ha : ∀j,A (columnSlots j)=col j)
    (hbank : col 6=OrderedPacketStep.bank C R ps) (hcount : col 7=CompareMachine.word (n+1)) :
    ∀j,finishedBank C R n ps A (columnSlots j)=col j := by
  intro j
  by_cases h6:j=6
  · subst j
    change finishedBank C R n ps A (majoritySlots 44)=_
    rw [ready_majority_words,MajorityComplete.Bootstrap.readyWith,MajorityComplete.Bootstrap.source_data]
    exact hbank.symm
  by_cases h7:j=7
  · subst j
    change install coldSlots A (MajorityComplete.Cold.result C R n ps) (coldSlots 146)=_
    rw [install_slot coldSlots cold_injective,MajorityComplete.Cold.result_count]
    exact hcount.symm
  · have away : ∀k,coldSlots k≠columnSlots j := by
      intro k he
      rcases column_cold_overlap j k he.symm with hp|hp
      · exact h6 hp.1
      · exact h7 hp.1
    rw [finishedBank,install_other _ _ _ _ away]
    exact ha j

theorem ready_column_heads (H : Fin 742→Nat)
    (hh : ∀j,H (columnSlots j)=Function.update (TranscriptColumn.heads 0 0) 7 0 j) :
    ∀j,readyHeads H (columnSlots j)=TranscriptColumn.heads 0 0 j := by
  intro j
  by_cases h6:j=6
  · subst j
    change readyHeads H (majoritySlots 44)=_
    rw [ready_majority_heads]
    rfl
  by_cases h7:j=7
  · subst j;exact Function.update_self _ _ _
  · have away : ∀k,coldSlots k≠columnSlots j := by
      intro k he
      rcases column_cold_overlap j k he.symm with hp|hp
      · exact h6 hp.1
      · exact h7 hp.1
    have h709 : columnSlots j≠709 := by
      intro he
      apply h7
      exact column_injective he
    rw [readyHeads,Function.update_of_ne h709,finishedHeads,dockH_other _ _ _ _ away,hh,
      Function.update_of_ne h7]

end
end Theorem25Completion.WalkLiteralProducedMajority
