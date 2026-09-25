import Proof.CaseAnalysis.RowsModeCacheHash
import Proof.CaseAnalysis.RowsTupleSeekDock

/-! The actual computed flags and live original mask cursor enter the
literal pair writer; the child count remains independent of the mask. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def selectMachine (mode : Fin 3):=RecoveryFocus.machine selectSlots (CloseoutRowsModeLiteralSelect.machine mode)

theorem selected_heads (mode : Fin 3) (p : Parameters) (s : State) :
    heads (selected mode p s)=Function.update (heads s) 23 (s.children+s.child.toNat+1):=by
  funext i;fin_cases i <;> rfl

theorem selected_data (mode : Fin 3) (p : Parameters) (s : State) :
    data p (selected mode p s) true=
      Function.update (Function.update (Function.update (data p s true)
        16 [(selected mode p s).var]) 17 [(selected mode p s).neg])
          23 (RepairSource.VerifierDecoding.CompareMachine.word (s.children+s.child.toNat)):=by
  funext i;fin_cases i <;> rfl

theorem select_run (mode : Fin 3) (p : Parameters) (s : State) :
    Step (selectMachine mode) 1 (heads s) (data p s true)
      (heads (selected mode p s)) (data p (selected mode p s) true):=by
  have hi:Function.Injective selectSlots:=by decide
  have r:=CloseoutRowsModeLiteralScan.scan_run mode s.zero s.sibling s.child s.var s.neg p.mask s.index s.children
  apply CloseoutRowsTupleSeek.dock_exact r selectSlots hi (heads s) (heads (selected mode p s))
    (data p s true) (data p (selected mode p s) true)
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i h
    have h16:i≠16:=by intro he;exact h 4 he.symm
    have h17:i≠17:=by intro he;exact h 5 he.symm
    have h23:i≠23:=by intro he;exact h 6 he.symm
    rw [selected_heads,selected_data]
    simp only [Function.update_of_ne h16,Function.update_of_ne h17,Function.update_of_ne h23,and_self]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
