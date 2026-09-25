import Proof.CaseAnalysis.WitnessTermRoundFinish

/-! The retained-field reader and actual circuit receipt now join the
complete successful term controller. The circuit supplier is explicit;
its output is not decoded or copied a second time. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem continue_run {t s n fuel : ℕ} (p : Machine t s)
    (source middle : Configuration t s) (last : ExecutionReceipt t s)
    (hp : Timed p n source middle) (hr : runFrom p fuel middle=some last) :
    ∃ r,runFrom p (n+fuel) source=some r ∧ r.steps=n+last.steps ∧
      r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes := by
  rcases hp with ⟨space,hp⟩
  obtain ⟨r,run,rf,rs,_⟩ := hp.followedBy last hr
  exact ⟨r,run,rs,by rw [rf],by rw [rf]⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
