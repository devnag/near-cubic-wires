import Proof.Rows.SourceDockCore
import Proof.Packets.PacketsXMajorityCompleteLayout

/-! The complete majority computation restores the original head layout.
Only the two generated-bank cursors move, and both are physically returned. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open Completion.SourceDock
noncomputable section

private theorem dockH_local_update {t u : Nat} (slots : Fin t→Fin u)
    (hi : Function.Injective slots) (ambient : Fin u→Nat) (localHeads : Fin t→Nat)
    (j : Fin t) (value : Nat) :
    dockH slots ambient (Function.update localHeads j value)=
      Function.update (dockH slots ambient localHeads) (slots j) value := by
  funext i
  by_cases h : i=slots j
  · subst i
    rw [dockH_slot slots hi,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne h]
    unfold dockH
    cases hp : RecoveryFocus.pick slots i with
    | none=>rfl
    | some k=>
      have hkj : k≠j := by
        intro he;subst k
        exact h (RecoveryFocus.slot_of_pick slots hp).symm
      exact Function.update_of_ne hkj value localHeads

private theorem enumerationH_update (out : List Bool) :
    enumerationH out=Function.update (enumerationH []) 43 out.length := by
  funext i;fin_cases i <;>rfl

private theorem producedH_update (C R : Nat) (ps : List (Ring.Poly Nat)) :
    producedH C R ps=Function.update inputH 37 (paired C R ps).length := by
  funext i;fin_cases i <;>rfl

theorem paired_ready_heads (C R : Nat) (ps : List (Ring.Poly Nat)) : pairedReadyH C R ps=inputH := by
  rw [pairedReadyH,producedH_update,Function.update_idem]
  exact Function.update_eq_self 37 inputH

theorem fold_ready_heads (C R : Nat) (ps : List (Ring.Poly Nat)) : foldReadyH C R ps=inputH := by
  have same : dockH enumSlots (pairedReadyH C R ps) (enumerationH [])=pairedReadyH C R ps :=
    heads_existing enumSlots _ _ (enum_entry_heads C R ps)
  rw [foldReadyH,enumeratedH,enumerationH_update,dockH_local_update enumSlots enum_injective,same]
  change Function.update (Function.update (pairedReadyH C R ps) 82 (termBank C R ps).length) 82 0=inputH
  rw [Function.update_idem,paired_ready_heads]
  exact Function.update_eq_self 82 inputH

theorem final_heads (C R : Nat) (ps : List (Ring.Poly Nat)) : finalH C R ps=inputH := by
  rw [finalH,heads_existing foldSlots _ _ (fold_entry_heads C R ps),fold_ready_heads]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
