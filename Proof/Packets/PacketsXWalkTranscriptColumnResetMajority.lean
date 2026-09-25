import Proof.Packets.PacketsXWalkTranscriptColumnConsume

/-! Restore the actual majority private arena, erase the consumed shared
column, and physically increment the candidate word. The stored result bank
survives all three operations. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumnArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Completion.SourceDock Theorem25Completion.CycleBounds
noncomputable section

def resetMajority := RecoveryFocus.machine majoritySlots MajorityComplete.Bootstrap.reset
def finish := Composition.machine resetMajority resetColumn
def finishBudget (R F T index : Nat) := 4*F+14+TranscriptColumn.resetBudget R T index

theorem reset_computed (palette : Fin 10→List Bool) (C R F N T S index : Nat)
    (source target result : List Bool) (old : PacketVector.Packet) (ps : List (Ring.Poly Nat))
    (hf : MajorityComplete.Palette.Fits C R ps.length F)
    (hc : MajorityComplete.Bootstrap.Compatible palette C R ps.length F)
    (hwork : ∀i,(MajorityComplete.Bootstrap.finalWork C R F ps i).length≤F)
    (H : Fin 471→Nat) (A : Fin 471→List Bool) (hh : ReadyHeads H result.length)
    (ha : Computed palette C R F N T S index source old target result ps A) :
    ∃B,Step resetMajority (4*F+13) H A H B ∧
      Ready palette C R F N T S index source old target result ps B := by
  have localRun:=MajorityComplete.Bootstrap.reset_with palette C R F ps
    (MajorityComplete.Bootstrap.finalWork C R F ps) hwork hf hc
  have actual:=dock localRun majoritySlots majority_injective H A hh.majority ha.majority
  rw [heads_existing majoritySlots H _ hh.majority] at actual
  refine ⟨_,actual,?_,?_,?_⟩
  · intro j
    rw [majority_keeps_column]
    · exact ha.column j
    · change MajorityComplete.Bootstrap.data _ _ _ _ 44=A (columnSlots 6)
      rw [MajorityComplete.Bootstrap.source_data,←majority_source,ha.majority 44,
        MajorityComplete.Bootstrap.source_with]
  · intro j _;exact install_slot majoritySlots majority_injective _ _ j
  · rw [majority_install_result,ha.result]

theorem finish_run (palette : Fin 10→List Bool) (C R F N T S index : Nat)
    (source target result : List Bool) (old : PacketVector.Packet) (ps : List (Ring.Poly Nat))
    (hf : MajorityComplete.Palette.Fits C R ps.length F)
    (hc : MajorityComplete.Bootstrap.Compatible palette C R ps.length F)
    (hwork : ∀i,(MajorityComplete.Bootstrap.finalWork C R F ps i).length≤F)
    (H : Fin 471→Nat) (A : Fin 471→List Bool) (hh : ReadyHeads H result.length)
    (ha : Computed palette C R F N T S index source old target result ps A)
    (hlen : target.length=T*(2*R)) :
    ∃B,Step finish (finishBudget R F T index) H A H B ∧
      Ready palette C R F N T S (index+1) source old (List.replicate (T*(2*R)) false) result ps B := by
  obtain ⟨middle,first,hm⟩:=reset_computed palette C R F N T S index source target result old ps
    hf hc hwork H A hh ha
  obtain ⟨out,last,ho⟩:=reset_ready palette C R F N T S index source target result old ps H middle hh hm hlen
  refine ⟨out,?_,ho⟩
  simpa only [finish,finishBudget,show 4*F+13+1=4*F+14 by omega] using first.seq last

end
end Theorem25Completion.WalkTranscriptColumnArena
