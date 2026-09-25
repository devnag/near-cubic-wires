import Proof.CaseAnalysis.RowsModeElementaryLayout

/-! The reusable boundary contains erased work cells, the unchanged numeric
masters, and the live append cursor. No monomial stream is supplied here. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryLayout
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flatBlank (w k M C : Nat) (out : List Bool) : Fin 52→List Bool:=
  Fin.addCases (m:=46) (n:=6) (motive:=fun _=>List Bool)
    (fun i=>if i=44 then out else List.replicate C false) (extra w k M C)

theorem loaded_core (w k M C : Nat) (out : List Bool) (i : Fin 45) :
    (loaded w k M C out).tapes (i.castAdd 7)=
      ZeroPadding.pad (CloseoutRowsModeElementaryReset.caps C i) (CloseoutRowsModeElementary.input w k M out i):=
by
  change (loaded w k M C out).tapes ((i.castAdd 1).castAdd 6)=_
  simp only [loaded,TapeEmbedding.config,Fin.addCases_left,CloseoutRowsModeElementaryReset.input,
    ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,ZeroPadding.pad_zero]
  rfl

theorem blank_old (w k M C : Nat) (out : List Bool) (i : Fin 45) :
    blank w k M C out (i.castAdd 7)=if i=44 then out else List.replicate C false:=by
  fin_cases i
  all_goals first
    | exact CloseoutRowsModeElementaryReload.data_dest _ _ _ 0 0
    | exact CloseoutRowsModeElementaryReload.data_dest _ _ _ 0 1
    | exact CloseoutRowsModeElementaryReload.data_dest _ _ _ 0 2
    | exact CloseoutRowsModeElementaryReload.data_dest _ _ _ 0 3
    | (rw [blank,CloseoutRowsModeElementaryReload.data_other _ _ _ _ _ (by decide),loaded_core]
       simp [CloseoutRowsModeElementaryReset.caps,CloseoutRowsModeElementaryReset.selected,
         CloseoutRowsModeElementary.input,CloseoutRowsModeElementary.extraTapes,
         RowTupleEnumerationReady.input,RowTupleDerivedEnumeration.input,Fin.addCases,ZeroPadding.pad])

theorem blank_eq (w k M C : Nat) (out : List Bool) : blank w k M C out=flatBlank w k M C out:=by
  funext i
  refine Fin.addCases (m:=45) (n:=7) (fun j=>?_) (fun j=>?_) i
  · rw [blank_old]
    simp [flatBlank,Fin.addCases,show j.val<46 by omega,Fin.ext_iff]
  · fin_cases j
    all_goals
      rw [blank,CloseoutRowsModeElementaryReload.data_other _ _ _ _ _ (by decide)]
      rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryLayout
