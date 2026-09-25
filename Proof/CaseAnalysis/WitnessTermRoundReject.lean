import Proof.CaseAnalysis.WitnessTermRoundRun

/-! A false circuit verdict shares the reader/circuit prefix, folds into
the original term verdict, and stops through the existing false exit.
No mass update, coefficient append or outer circuit clear is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
open private stopped_run from Proof.CaseAnalysis.WitnessTermRoundFinish

private theorem data_update (P : ℕ) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (out bits : List Bool) (extra : Fin 1705 → List Bool) :
    Function.update (data P terms ambient out extra) 719 bits=
      data P (Function.update terms 719 bits) ambient out extra := by
  funext i
  refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=826) (n:=1) ?_ ?_ j
    · intro k
      refine Fin.addCases (m:=725) (n:=101) ?_ ?_ k
      · intro l
        by_cases hl : l=719
        · subst l
          change Function.update (data P terms ambient out extra) (719 : Fin 2532) bits 719=
            Function.update terms (719 : Fin 725) bits 719
          rw [Function.update_self,Function.update_self]
        · have hi : (((l.castAdd 101).castAdd 1).castAdd 1705 : Fin 2532)≠719 := by
            intro h;apply hl;exact Fin.ext (congrArg (fun z : Fin 2532=>z.val) h)
          rw [Function.update_of_ne hi]
          simp only [data,Fin.addCases_left]
          change TermCommit.data _ _ _ _ (TermCommit.eraseSlots l)=TermCommit.data _ _ _ _ (TermCommit.eraseSlots l)
          rw [TermCommit.data_core,TermCommit.data_core,Function.update_of_ne hl]
      · intro l
        rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change 725+l.val≠719;omega)]
        simp only [data,TermCommit.data,Fin.addCases_left,TermMass.data,Fin.addCases_right]
    · intro k
      rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change 826+k.val≠719;omega)]
      simp only [data,Fin.addCases_left,TermCommit.data,Fin.addCases_right]
  · intro j
    rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change 827+j.val≠719;omega)]
    simp only [data,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
