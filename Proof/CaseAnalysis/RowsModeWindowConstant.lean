import Proof.CaseAnalysis.RowsModeWindowLayout

/-! The zero-population/zero-degree branch writes the exact constant raw
monomial body. This two-byte literal is part of the fixed ordinary program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowConstant
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1→Fin 60:=fun _=>44
noncomputable def machine:=RecoveryFocus.machine slots (HierarchyFixedWord.raw [true,false])

theorem append_run (H : Fin 60→Nat) (A : Fin 60→List Bool) (out : List Bool)
    (hH : H 44=out.length) (hA : A 44=out) :
    Step machine 2 H A (Function.update H 44 (out++[true,false]).length)
      (Function.update A 44 (out++[true,false])):=by
  obtain ⟨a,ha,af,as⟩:=Constants.write_run [true,false] out
  obtain ⟨r,hr,_,_,rh,rt,keep⟩:=RecoveryFocus.dock slots (by intro i j _;exact Subsingleton.elim i j)
    (HierarchyFixedWord.raw [true,false]) _ H A (Constants.cfg [true,false] out 0 (by decide))
    (by intro i;simpa [Constants.cfg,slots] using hH) (by intro i;simpa [Constants.cfg,slots] using hA) a ha
  refine Step.of_run hr ?_ ?_
  · funext i
    by_cases hi:i=44
    · subst i
      have h:=rh 0
      rw [af] at h
      simpa [Constants.cfg,slots] using h
    · rw [(keep i (fun _=>Ne.symm hi)).1]
      simp [hi]
  · funext i
    by_cases hi:i=44
    · subst i
      have h:=rt 0
      rw [af] at h
      simpa [Constants.cfg,slots] using h
    · rw [(keep i (fun _=>Ne.symm hi)).2]
      simp [hi]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowConstant
