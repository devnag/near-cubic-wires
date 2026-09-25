import Proof.CaseAnalysis.WitnessTermRoundFlag

/-! A successful literal term commits its original coefficient and clears
exactly the private circuit bank. This is the actual last two calls of the
fixed term controller; the failed exit never uses this clearing receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem reset_external (j : Fin 1699) :
    ∃ i : Fin 1705,TermCircuitReset.slots j=i.natAdd 827 := by
  have hlow : 827 ≤ (TermCircuitReset.slots j).val := by
    unfold TermCircuitReset.slots
    split_ifs
    · change 827 ≤ 827+_
      omega
    · change 827 ≤ j.val+833
      omega
  refine ⟨⟨(TermCircuitReset.slots j).val-827,by have h:=(TermCircuitReset.slots j).isLt;omega⟩,?_⟩
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

private theorem stopped_run {t k n : ℕ} (sizes : Fin k → ℕ)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))
    (input : Configuration t (Fintype.card (RecoveryCalls.Control sizes)))
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool)
    (h : Timed (RecoveryCalls.machine sizes programs entry next) n input
      (RecoveryCalls.stopped sizes heads tapes)) :
    ∃ r,runFrom (RecoveryCalls.machine sizes programs entry next) n input=some r ∧
      r.steps=n ∧ r.final.heads=heads ∧ r.final.tapes=tapes := by
  obtain ⟨r,hr,rf,rs⟩ := h.run (by
    simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
  exact ⟨r,hr,rs,by rw [rf];rfl,by rw [rf];rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
