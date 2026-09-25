import Proof.CaseAnalysis.RowsModeCacheInit

/-! Whole actual cache population from original numeric/seed/mask fields,
including its own unary-index initialization and head-zero loop entry. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sourceMachine (mode : Fin 3):=Composition.machine initMachine (machine mode)
def sourceWord (mode : Fin 3) (p : Parameters) (count : Nat):=
  (List.range count).flatMap (piece mode p (initialState []))
def sourceBudget (p : Parameters) (count : Nat):=4+budget p (initialState []) count

theorem source_step (mode : Fin 3) (p : Parameters) (count : Nat) (out : List Bool)
    (hl : p.level ≤ p.rank) (hC : p.rank+2 ≤ p.C) (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2 ≤ p.C)
    (hi : count ≤ 2^p.rank) :
    Step (sourceMachine mode) (sourceBudget p count) (initHeads out 0) (initData p count out 0)
      (loopHeads (atState mode p (initialState []) count (out++sourceWord mode p count)))
      (loopData p (atState mode p (initialState []) count (out++sourceWord mode p count)) count):=by
  obtain ⟨r,hr,rf,_⟩:=loop_run mode p (initialState []) count out hl hC hb (by simpa [initialState] using hi)
  have b:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact (init_run p count out).seq b

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
