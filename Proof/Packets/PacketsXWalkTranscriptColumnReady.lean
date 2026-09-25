import Proof.Packets.WalkTranscriptColumnArenaFrame
import Proof.Packets.PacketsXWalkTranscriptColumnMajorityResident

/-! A concrete resident-data invariant for the direct candidate loop.
It pins actual words and the accumulated output; it contains no execution
premise and permits the shared bank to be either filled or physically zeroed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptColumnArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

structure Ready (palette : Fin 10→List Bool) (C R F N T S index : Nat) (source : List Bool) (old : PacketVector.Packet)
    (target result : List Bool) (ps : List (Ring.Poly Nat)) (A : Fin 471→List Bool) : Prop where
  column : ∀j,A (columnSlots j)=TranscriptColumn.residentTapes R N T index S source
    (PacketVector.payload R old) (PacketVector.count R old) target j
  majority : ∀j,j≠44→A (majoritySlots j)=MajorityComplete.Bootstrap.readyWith palette C R F ps j
  result : A 29=result

structure ReadyHeads (H : Fin 471→Nat) (outputLength : Nat) : Prop where
  column : ∀j,H (columnSlots j)=TranscriptColumn.heads 0 0 j
  majority : ∀j,H (majoritySlots j)=MajorityComplete.Bootstrap.heads j
  result : H 29=outputLength

theorem Ready.majority_pin {palette : Fin 10→List Bool} {C R F N T S index : Nat} {source target result : List Bool}
    {old : PacketVector.Packet} {ps : List (Ring.Poly Nat)} {A : Fin 471→List Bool}
    (h : Ready palette C R F N T S index source old target result ps A)
    (ht : target=OrderedPacketStep.bank C R ps) :
    ∀j,A (majoritySlots j)=MajorityComplete.Bootstrap.readyWith palette C R F ps j := by
  intro j
  by_cases hj : j=44
  · subst j
    rw [majority_source,h.column 6]
    change target=MajorityComplete.Bootstrap.data _ _ _ _ 44
    rw [MajorityComplete.Bootstrap.source_data]
    exact ht
  · exact h.majority j hj

theorem Ready.change_polys {palette : Fin 10→List Bool} {C R F N T S index : Nat} {source target result : List Bool}
    {old : PacketVector.Packet} {ps qs : List (Ring.Poly Nat)} {A : Fin 471→List Bool}
    (h : Ready palette C R F N T S index source old target result ps A)
    (hRF : R+3≤F) (hCF : C≤F) (hlen : ps.length=qs.length) :
    Ready palette C R F N T S index source old target result qs A := by
  refine ⟨h.column,?_,h.result⟩
  intro j hj
  rw [WalkTranscriptColumnMajoritySource.ready_with_source palette C R F ps qs hRF hCF hlen,
    Function.update_of_ne hj]
  exact h.majority j hj

theorem extract_ready (palette : Fin 10→List Bool) (C R F N T S : Nat) (rows : Nat→List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N) (old : PacketVector.Packet)
    (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P) (hold : PacketVector.Fits R old)
    (ps : List (Ring.Poly Nat)) (result : List Bool) (H : Fin 471→Nat) (A : Fin 471→List Bool)
    (hh : ReadyHeads H result.length)
    (ha : Ready palette C R F N T S column.val (PacketTranscript.prefixBank R rows T) old
      (List.replicate (T*(2*R)) false) result ps A) :
    ∃B,Step extract (TranscriptColumn.budget R N T column.val) H A H B ∧
      Ready palette C R F N T S column.val (PacketTranscript.prefixBank R rows T)
        (TranscriptColumn.previous (TranscriptColumn.rowPacket N rows hlen column) old T)
        (PacketVector.bank R (List.ofFn (fun i : Fin T=>TranscriptColumn.rowPacket N rows hlen column i.val)))
        result ps B := by
  have actual:=extract_run R N T S rows hlen column old hfit hold H A hh.column ha.column
  refine ⟨_,actual,?_,?_,?_⟩
  · intro j;exact install_slot columnSlots column_injective _ _ j
  · intro j hj
    rw [column_install_majority_private _ _ j hj]
    exact ha.majority j hj
  · rw [column_install_result,ha.result]

theorem reset_ready (palette : Fin 10→List Bool) (C R F N T S index : Nat) (source target result : List Bool)
    (old : PacketVector.Packet) (ps : List (Ring.Poly Nat)) (H : Fin 471→Nat) (A : Fin 471→List Bool)
    (hh : ReadyHeads H result.length) (ha : Ready palette C R F N T S index source old target result ps A)
    (hlen : target.length=T*(2*R)) :
    ∃B,Step resetColumn (TranscriptColumn.resetBudget R T index) H A H B ∧
      Ready palette C R F N T S (index+1) source old (List.replicate (T*(2*R)) false) result ps B := by
  have actual:=reset_run R N T index S source (PacketVector.payload R old) (PacketVector.count R old)
    target hlen H A hh.column ha.column
  refine ⟨_,actual,?_,?_,?_⟩
  · intro j;exact install_slot columnSlots column_injective _ _ j
  · intro j hj
    rw [column_install_majority_private _ _ j hj]
    exact ha.majority j hj
  · rw [column_install_result,ha.result]

end
end Theorem25Completion.WalkTranscriptColumnArena
