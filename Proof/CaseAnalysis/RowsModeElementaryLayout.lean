import Proof.CaseAnalysis.RowsModeElementaryReload
import Proof.CaseAnalysis.RowsModeElementaryClear

/-! The reusable elementary bank has four original numeric master tapes,
an original coarse C driver, and one shared erase/copy log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryLayout
open LocalBitMultitape RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def metadata (w k M : Nat) : Fin 4→List Bool:=
  ![CompareMachine.word w,frame (binary w (M-1)),CompareMachine.word k,List.replicate w true]
def extra (w k M C : Nat) : Fin 6→List Bool:=
  Fin.addCases (m:=4) (n:=2) (motive:=fun _=>List Bool) (metadata w k M)
    ![List.replicate C true,List.replicate (C+1) false]
noncomputable def raw (w k M : Nat) (out : List Bool):=
  (⟨CloseoutRowsModeElementary.machine.start,CloseoutRowsModeElementary.heads out,
    CloseoutRowsModeElementary.input w k M out⟩ : Configuration 45 _)
noncomputable def loaded (w k M C : Nat) (out : List Bool):=
  TapeEmbedding.config (fun _ : Fin 6=>0) (extra w k M C)
    (CloseoutRowsModeElementaryReset.input (raw w k M out) C)
def heads (out : List Bool) (i : Fin 52):=if i=44 then out.length else 0
noncomputable def blank (w k M C : Nat) (out : List Bool):=
  CloseoutRowsModeElementaryReload.data (loaded w k M C out).tapes C (metadata w k M) 0

theorem loaded_heads (w k M C : Nat) (out : List Bool) :
    (loaded w k M C out).heads=heads out:=by
  funext i;fin_cases i <;> rfl

theorem loaded_dest (w k M C : Nat) (out : List Bool) (j : Fin 4) :
    (loaded w k M C out).tapes (CloseoutRowsModeElementaryReload.dest j)=
      ZeroPadding.pad C (metadata w k M j):=by
  fin_cases j <;> exact ZeroPadding.pad_zero _

theorem loaded_master (w k M C : Nat) (out : List Bool) (j : Fin 4) :
    (loaded w k M C out).tapes (CloseoutRowsModeElementaryReload.source j)=metadata w k M j:=by
  fin_cases j <;> rfl

theorem reload_complete (w k M C : Nat) (out : List Bool) :
    CloseoutRowsModeElementaryReload.data (loaded w k M C out).tapes C (metadata w k M) 4=
      (loaded w k M C out).tapes:=by
  funext i
  cases hp:RecoveryFocus.pick CloseoutRowsModeElementaryReload.dest i with
  | none=>simp only [CloseoutRowsModeElementaryReload.data,hp]
  | some j=>
    have hi:=RecoveryFocus.slot_of_pick CloseoutRowsModeElementaryReload.dest hp
    subst i
    simp only [CloseoutRowsModeElementaryReload.data_dest,j.isLt,if_true,loaded_dest]

theorem reload_run (w k M C : Nat) (out : List Bool) (hmeta : 2*w+k+3≤C) :
    ∃ r,runFrom CloseoutRowsModeElementaryReload.machine (4*(2*C+5))
      ⟨CloseoutRowsModeElementaryReload.machine.start,heads out,blank w k M C out⟩=some r ∧
      r.final.heads=heads out ∧ r.final.tapes=(loaded w k M C out).tapes ∧ r.steps≤4*(2*C+5):=by
  obtain ⟨r,hr,rh,rt,rs⟩:=CloseoutRowsModeElementaryReload.reload_run
    (loaded w k M C out).tapes (heads out) C (metadata w k M)
    (loaded_master w k M C out) (by
      intro i;fin_cases i <;> simp [metadata,CompareMachine.word,frame_length,binary_length] <;> omega)
    (by rfl) (by rfl) (by intro j i;fin_cases j <;> fin_cases i <;> rfl)
  exact ⟨r,hr,rh,rt.trans (reload_complete w k M C out),rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryLayout
