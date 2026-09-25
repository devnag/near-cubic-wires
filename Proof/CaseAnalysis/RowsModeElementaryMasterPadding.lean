import Proof.CaseAnalysis.RowsModeElementaryReusable

/-! Fixed zero padding on the retained numeric masters permits physical
counter overwrites between degree calls. The growing output is unpadded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReusable
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsModeElementaryLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def masterCaps (C : Nat) (i : Fin 52) : Nat := if 46 ≤ i.val ∧ i.val < 50 then C else 0
noncomputable def paddedBlank (w k M C : Nat) (out : List Bool) : Fin 52→List Bool:=
  fun i=>ZeroPadding.pad (masterCaps C i) (blank w k M C out i)

theorem padded_run (w k M C : Nat) (out : List Bool) (hM : 0<M) (hMw : M≤2^w)
    (hmeta : 2*w+k+3≤C) (hC : CloseoutRowsModeElementary.budget w k M+1≤C) :
    Step machine (budget w k M C) (heads out) (paddedBlank w k M C out)
      (heads (out++CloseoutRowsModeElementary.bodyWord w k M))
      (paddedBlank w k M C (out++CloseoutRowsModeElementary.bodyWord w k M)):=by
  obtain ⟨r,hr,rh,rt,_⟩:=reusable_run w k M C out hM hMw hmeta hC
  exact (Step.of_run hr rh rt).pad (masterCaps C)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReusable
