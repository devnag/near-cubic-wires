import Proof.CaseAnalysis.RowsModeCacheReuseData

/-! One complete cache pass returns every head except the live append.
The paid recording capacity is separate from the hash workspace capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reuseSelected (i : Fin 25):=decide (i≠20)
noncomputable def reuseReturn (mode : Fin 3):=
  TapeEmbedding.machine 2 (MaskedReset.machine (sourceMachine mode) reuseSelected)

theorem reuse_return (mode : Fin 3) (p : Parameters) (M R D : Nat) (out : List Bool)
    (hl : p.level ≤ p.rank) (hC : p.rank+2 ≤ p.C) (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2 ≤ p.C)
    (hi : M ≤ 2^p.rank) (hR : sourceBudget p M ≤ R)
    (hD : p.C+1 ≤ D) (hr : p.rank+1 ≤ D) (hd : 3 ≤ D) :
    Step (reuseReturn mode) (2*sourceBudget p M+2)
      (reuseHeads out) (reuseData p M R D out (fun _=>List.replicate D false))
      (reuseHeads (out++sourceWord mode p M))
      (reuseData p M R D (out++sourceWord mode p M) (reuseFinal mode p M D)):=by
  have raw:=((source_step mode p M out hl hC hb hi).pad (reuseCaps D)).mask reuseSelected
    (by intro i hi;simp only [reuseSelected,decide_eq_true_eq] at hi;simp [initHeads,hi]) hR
  have lifted:=raw.embed (fun _ : Fin 2=>0) (![List.replicate D true,List.replicate (D+1) false])
  apply (lifted.congr_in ?_ ?_).congr ?_ ?_
  · funext i;fin_cases i <;> rfl
  · exact reuse_lift p M R D out _ _ (reuse_initial_old p M R D out hD hr hd)
  · funext i;fin_cases i <;> rfl
  · exact reuse_lift p M R D _ _ _ (reuse_final_old p M R D (track mode p (initialState []) M) _)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
