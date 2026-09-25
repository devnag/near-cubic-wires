import Proof.Packets.WalkTranscriptColumnArena

/-! The packet-store stage changes exactly the accumulating output bank.
In particular every shared-column and majority-private tape and head is
preserved at the documented reset boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptColumnArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed.Materializer Completion.SourceDock
noncomputable section

private theorem install_local_update {t u : Nat} (ports : Fin t→Fin u)
    (hi : Function.Injective ports) (A : Fin u→List Bool) (a : Fin t→List Bool)
    (j : Fin t) (word : List Bool) :
    install ports A (Function.update a j word)=Function.update (install ports A a) (ports j) word := by
  funext i
  by_cases he : i=ports j
  · subst i;rw [install_slot ports hi,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne he]
    unfold install
    cases hp : RecoveryFocus.pick ports i with
    | none=>rfl
    | some k=>
      have hk : k≠j := by
        intro h;subst k;exact he (RecoveryFocus.slot_of_pick ports hp).symm
      exact Function.update_of_ne hk word a

private theorem heads_local_update {t u : Nat} (ports : Fin t→Fin u)
    (hi : Function.Injective ports) (H : Fin u→Nat) (h : Fin t→Nat)
    (j : Fin t) (pos : Nat) :
    dockH ports H (Function.update h j pos)=Function.update (dockH ports H h) (ports j) pos := by
  funext i
  by_cases he : i=ports j
  · subst i;rw [dockH_slot ports hi,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne he]
    unfold dockH
    cases hp : RecoveryFocus.pick ports i with
    | none=>rfl
    | some k=>
      have hk : k≠j := by
        intro h;subst k;exact he (RecoveryFocus.slot_of_pick ports hp).symm
      exact Function.update_of_ne hk pos h

private theorem store_tapes_update (R column F S : Nat) (old word : List Bool) (P : PacketVector.Packet) :
    WalkTranscriptColumnStore.paddedTapes R column F S word P=
      Function.update (WalkTranscriptColumnStore.paddedTapes R column F S old P) 1 word := by
  funext i;fin_cases i <;>rfl

private theorem store_heads_update (old pos : Nat) :
    PacketBank.H pos 0=Function.update (PacketBank.H old 0) 1 pos := by
  funext i;fin_cases i <;>rfl

theorem store_run_update (R column F S : Nat) (bank : List Bool) (P : PacketVector.Packet)
    (hP : PacketVector.Fits R P) (H : Fin 471 → Nat) (A : Fin 471 → List Bool)
    (hh : ∀j,H (storeSlots j)=PacketBank.H bank.length 0 j)
    (ha : ∀j,A (storeSlots j)=WalkTranscriptColumnStore.paddedTapes R column F S bank P j) :
    Step storeResult (WalkTranscriptColumnStore.budget R) H A
      (Function.update H 29 (bank++PacketVector.entry R P).length)
      (Function.update A 29 (bank++PacketVector.entry R P)) := by
  have h:=store_run R column F S bank P hP H A hh ha
  rw [store_tapes_update R column F S bank,install_local_update storeSlots store_injective,
    install_existing storeSlots A _ ha] at h
  rw [store_heads_update bank.length,heads_local_update storeSlots store_injective,
    heads_existing storeSlots H _ hh] at h
  exact h

end
end Theorem25Completion.WalkTranscriptColumnArena
