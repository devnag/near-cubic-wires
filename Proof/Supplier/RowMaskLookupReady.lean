import Proof.Supplier.RowMaskLookupReusable

/-! Selected-mask output ready for the common coefficient consumer. The
occurrence word is physically rewound, and its actual count returns to head1. -/
namespace NearCubicWires.RepairOrdinary.RowMaskLookupReady
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts RowMaskConsume
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true



theorem count_run (count : ℕ) :
    ∃ r,runFrom UnaryTemplate.machine (count+2) (UnaryTemplate.config 0 (CompareMachine.word count) (count+1))=some r ∧
      r.final=UnaryTemplate.config 2 (CompareMachine.word count) 1 ∧ r.steps=count+2 := by
  have hp := UnaryTemplate.return_prefix (CompareMachine.word count) count (by rfl)
    (by intro k hk; simp [CompareMachine.read_mark,hk])
  have h := Prefix.step (by simp : (UnaryTemplate.config 0 (CompareMachine.word count) (count+1)).tapeCells≤
      (CompareMachine.word count).length) (by rfl) (UnaryTemplate.start_step (CompareMachine.word count) count) hp
  obtain ⟨r,hr,rf,rs,_⟩ := h.run (by rfl) (by simp)
  exact ⟨r,by simpa [Nat.add_assoc] using hr,rf,by omega⟩

end NearCubicWires.RepairOrdinary.RowMaskLookupReady
