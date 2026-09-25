import Proof.Packets.TranscriptColumnReset
import Proof.Packets.WalkTranscriptColumnStore
import Proof.Rows.SourceDockCore

/-! Shared resident arena for the direct column-to-majority consumer.  The
column bank is the one shared tape; all majority work tapes are private.
The old cold-palette port 29 is reserved for the result bank in the worker;
the enclosing counted controller exchanges it with its final driver tape. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumnArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Completion.SourceDock
noncomputable section

def columnSlots : Fin 9 → Fin 471 := ![61,331,287,293,327,291,333,332,334]
def majoritySlots (j : Fin 137) : Fin 471 :=
  if j.val=44 then 333 else if hj : j.val<44 then ⟨335+j.val,by omega⟩ else ⟨334+j.val,by have h:=j.isLt;omega⟩
def storeSlots : Fin 6 → Fin 471 := ![461,29,456,457,334,291]

theorem column_injective : Function.Injective columnSlots := by decide
theorem store_injective : Function.Injective storeSlots := by decide
theorem majority_injective : Function.Injective majoritySlots := by
  intro i j he
  have hv := congrArg Fin.val he
  simp only [majoritySlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all only [Fin.val_natCast] <;> omega

theorem majority_source : majoritySlots 44=columnSlots 6 := rfl
theorem majority_private (j : Fin 137) (hj : j≠44) : 335≤(majoritySlots j).val := by
  have hv : j.val≠44 := by intro h;apply hj;exact Fin.ext h
  simp only [majoritySlots,hv,if_false]
  split_ifs <;> simp only <;> omega

theorem column_below (j : Fin 9) : (columnSlots j).val<335 := by
  fin_cases j <;> decide

theorem source_only_overlap (i : Fin 9) (j : Fin 137) (h : columnSlots i=majoritySlots j) :
    i=6 ∧ j=44 := by
  have hj : j=44 := by
    by_contra hj
    have lo := majority_private j hj
    have hi := column_below i
    have he := congrArg Fin.val h
    omega
  subst j
  have hi : i=6 := column_injective (h.trans majority_source)
  exact ⟨hi,rfl⟩

theorem majority_away_result (j : Fin 137) : majoritySlots j≠29 := by
  by_cases hj : j=44
  · subst j;decide
  · have h:=majority_private j hj
    intro he
    have hv:=congrArg Fin.val he
    change (majoritySlots j).val=29 at hv
    omega

theorem column_away_result (j : Fin 9) : columnSlots j≠29 := by fin_cases j <;> decide


def extract := RecoveryFocus.machine columnSlots TranscriptColumn.program
def resetColumn := RecoveryFocus.machine columnSlots TranscriptColumn.resetNext
def storeResult := RecoveryFocus.machine storeSlots WalkTranscriptColumnStore.machine

/-- Extraction over the genuinely reused zero backing of the shared bank. -/
theorem extract_run (R N T S : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N) (old : PacketVector.Packet)
    (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P) (hold : PacketVector.Fits R old)
    (H : Fin 471 → Nat) (A : Fin 471 → List Bool)
    (hh : ∀j,H (columnSlots j)=TranscriptColumn.heads 0 0 j)
    (ha : ∀j,A (columnSlots j)=TranscriptColumn.residentTapes R N T column.val S
      (PacketTranscript.prefixBank R rows T) (PacketVector.payload R old) (PacketVector.count R old)
      (List.replicate (T*(2*R)) false) j) :
    Step extract (TranscriptColumn.budget R N T column.val) H A H
      (install columnSlots A (TranscriptColumn.residentTapes R N T column.val S
        (PacketTranscript.prefixBank R rows T)
        (PacketVector.payload R (TranscriptColumn.previous (TranscriptColumn.rowPacket N rows hlen column) old T))
        (PacketVector.count R (TranscriptColumn.previous (TranscriptColumn.rowPacket N rows hlen column) old T))
        (PacketVector.bank R (List.ofFn (fun i : Fin T=>TranscriptColumn.rowPacket N rows hlen column i.val))))) := by
  have h := dock (TranscriptColumn.run_reuse R N T S rows hlen column old hfit hold)
    columnSlots column_injective H A hh ha
  rw [heads_existing columnSlots H _ hh] at h
  exact h

/-- The consumed column is physically cleared and the candidate word is
incremented, retaining the previous coordinate's packet operands. -/
theorem reset_run (R N T column S : Nat) (source payload count bank : List Bool)
    (hlen : bank.length=T*(2*R)) (H : Fin 471 → Nat) (A : Fin 471 → List Bool)
    (hh : ∀j,H (columnSlots j)=TranscriptColumn.heads 0 0 j)
    (ha : ∀j,A (columnSlots j)=TranscriptColumn.residentTapes R N T column S source payload count bank j) :
    Step resetColumn (TranscriptColumn.resetBudget R T column) H A H
      (install columnSlots A (TranscriptColumn.residentTapes R N T (column+1) S source payload count
        (List.replicate (T*(2*R)) false))) := by
  have h := dock (TranscriptColumn.reset_next R N T column S source payload count bank hlen)
    columnSlots column_injective H A hh ha
  rw [heads_existing columnSlots H _ hh] at h
  exact h

/-- Append exactly the majority packet before resetting its private arena.
The result-bank head alone advances; majority operand heads remain zero. -/
theorem store_run (R column F S : Nat) (bank : List Bool) (P : PacketVector.Packet)
    (hP : PacketVector.Fits R P) (H : Fin 471 → Nat) (A : Fin 471 → List Bool)
    (hh : ∀j,H (storeSlots j)=PacketBank.H bank.length 0 j)
    (ha : ∀j,A (storeSlots j)=WalkTranscriptColumnStore.paddedTapes R column F S bank P j) :
    Step storeResult (WalkTranscriptColumnStore.budget R) H A
      (dockH storeSlots H (PacketBank.H (bank++PacketVector.entry R P).length 0))
      (install storeSlots A (WalkTranscriptColumnStore.paddedTapes R column F S
        (bank++PacketVector.entry R P) P)) := by
  exact dock (WalkTranscriptColumnStore.run_padded R column F S bank P hP)
    storeSlots store_injective H A hh ha

end
end Theorem25Completion.WalkTranscriptColumnArena
