import Proof.CaseAnalysis.RowsModeElementaryReuse

/-! One actual reusable elementary call reloads the four numeric fields,
executes the complete cold subset writer, returns its heads, and clears its
work bank. The same retained C driver pays all four phases. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReusable
open LocalBitMultitape
open CloseoutRowsModeElementaryLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine CloseoutRowsModeElementaryReload.machine
  CloseoutRowsModeElementaryReuse.machine
def budget (w k M C : Nat):=4*(2*C+5)+1+CloseoutRowsModeElementaryReuse.budget w k M C

theorem reusable_run (w k M C : Nat) (out : List Bool) (hM : 0<M) (hMw : M≤2^w)
    (hmeta : 2*w+k+3≤C) (hC : CloseoutRowsModeElementary.budget w k M+1≤C) :
    ∃ r,runFrom machine (budget w k M C)
      ⟨machine.start,heads out,blank w k M C out⟩=some r ∧
      r.final.heads=heads (out++CloseoutRowsModeElementary.bodyWord w k M) ∧
      r.final.tapes=blank w k M C (out++CloseoutRowsModeElementary.bodyWord w k M) ∧
      r.steps≤budget w k M C:=by
  obtain ⟨a,ha,ah,atapes,_⟩:=reload_run w k M C out hmeta
  obtain ⟨b,hb,bh,bt,_⟩:=CloseoutRowsModeElementaryReuse.body_run w k M C out hM hMw hmeta hC
  have initial:(⟨CloseoutRowsModeElementaryReuse.machine.start,heads out,(loaded w k M C out).tapes⟩ :
      Configuration 52 _)=Composition.restart a.final CloseoutRowsModeElementaryReuse.machine.start:=by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact atapes.symm
  rw [initial] at hb
  have whole:=Composition.run_join CloseoutRowsModeElementaryReload.machine CloseoutRowsModeElementaryReuse.machine
    _ _ _ a b ha hb
  exact ⟨Composition.joinedReceipt a b,whole,bh,bt,runFrom_steps_le machine _ _ _ whole⟩

theorem budget_le (w k M C : Nat) (hmeta : 2*w+k+3≤C)
    (hC : CloseoutRowsModeElementary.budget w k M+1≤C) : budget w k M C≤16*(C+1):=by
  unfold budget CloseoutRowsModeElementaryReuse.budget CloseoutRowsModeElementaryReset.budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReusable
