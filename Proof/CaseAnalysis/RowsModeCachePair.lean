import Proof.CaseAnalysis.RowsModeCacheSelect

/-! The actual ordered literal pair append advances its own unary index and
masked count. The original hash label is advanced by the following stage. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def pairMachine:=RecoveryFocus.machine pairSlots CloseoutRowsModeLiteralPair.machine
def pairData (p : Parameters) (s : State) : Fin 24→List Bool:=
  Fin.addCases (m:=11) (n:=13) (motive:=fun _=>List Bool) (fields p s true) (extras p (emitted s))
def pairHeads (s : State) : Fin 24→Nat:=Function.update (heads (emitted s) 1) 11 s.index

theorem pair_heads_eq (s : State) :
    pairHeads s=Function.update (Function.update (Function.update (heads s) 16 1)
      19 (s.selectedCount+s.var.toNat+1)) 20 (s.out++pairWord s).length:=by
  funext i;fin_cases i <;> rfl

theorem pair_data_eq (p : Parameters) (s : State) :
    pairData p s=Function.update (Function.update (Function.update (Function.update (data p s true)
      17 [s.var]) 18 (UnaryTemplate.tape (s.index+2)))
      19 (RepairSource.VerifierDecoding.CompareMachine.word (s.selectedCount+s.var.toNat))) 20 (s.out++pairWord s):=by
  funext i;fin_cases i <;> rfl

theorem pair_run (p : Parameters) (s : State) :
    Step pairMachine (CloseoutRowsModeLiteralPair.budget s.index) (heads s) (data p s true)
      (pairHeads s) (pairData p s):=by
  have hi:Function.Injective pairSlots:=by decide
  have r:=CloseoutRowsModeLiteralPair.pair_run s.neg s.var [] [] s.out s.index s.selectedCount
  apply CloseoutRowsTupleSeek.dock_exact r pairSlots hi (heads s) (pairHeads s) (data p s true) (pairData p s)
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i h
    have h16:i≠16:=by intro he;exact h 0 he.symm
    have h17:i≠17:=by intro he;exact h 4 he.symm
    have h18:i≠18:=by intro he;exact h 1 he.symm
    have h19:i≠19:=by intro he;exact h 3 he.symm
    have h20:i≠20:=by intro he;exact h 2 he.symm
    rw [pair_heads_eq,pair_data_eq]
    simp only [Function.update_of_ne h16,Function.update_of_ne h17,Function.update_of_ne h18,
      Function.update_of_ne h19,Function.update_of_ne h20,and_self]

def cursorMachine : Machine 24 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if i=16 then .left else if i=11 then .right else .stay⟩ else none

theorem cursor_run (p : Parameters) (s : State) :
    Step cursorMachine 1 (pairHeads s) (pairData p s) (heads (emitted s)) (pairData p s):=by
  have hs:step cursorMachine ⟨0,pairHeads s,pairData p s⟩=some ⟨1,heads (emitted s),pairData p s⟩:=by
    simp only [step,cursorMachine,if_true]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,pairHeads,heads,extraHeads,emitted,Fin.addCases,HeadMove.apply]
    · rfl
  obtain ⟨r,hr,rf,_⟩:=(RecoveryExecution.Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
