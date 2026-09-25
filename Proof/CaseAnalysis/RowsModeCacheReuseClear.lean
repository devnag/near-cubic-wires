import Proof.CaseAnalysis.RowsModeCacheReusePorts

/-! One actual simultaneous erase prepares every private cache field.
Original inputs, the append output and the head-return log are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def reuseClear:=RecoveryFocus.machine reuseEraseSlots (RecoveryScratchErase.resetMachine 15)

theorem reuse_clear (p : Parameters) (M R D : Nat) (out : List Bool) (A : Fin 15→List Bool)
    (hA : ∀ i,(A i).length ≤ D) :
    Step reuseClear (2*D+4) (reuseHeads out) (reuseData p M R D out A)
      (reuseHeads out) (reuseData p M R D out (fun _=>List.replicate D false)):=by
  have r:=Step.of_ready (RecoveryScratchErase.erase_ready D (D+1) A hA)
  simp only [max_self] at r
  exact CloseoutRowsTupleSeek.dock_exact r reuseEraseSlots reuse_erase_injective _ _ _ _
    (reuse_erase_heads out) (reuse_erase_fields p M R D out A)
    (reuse_erase_heads out) (reuse_erase_fields p M R D out _)
    (fun i h=>⟨rfl,reuse_erase_keep p M R D out _ _ i h⟩)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
