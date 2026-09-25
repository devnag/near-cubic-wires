import Proof.CaseAnalysis.RowsModeCacheLoop

/-! The cache source starts at the original head-zero boundary. Three
actual steps write the constant unary index one and enter the retained
population and two empty counters. No caller supplies a literal-cache pair. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initialState (out : List Bool) : State:=⟨0,0,0,out,false,false,false,false,false⟩
def loopData (p : Parameters) (s : State) (count : Nat) : Fin 25→List Bool:=
  Fin.addCases (m:=24) (n:=1) (motive:=fun _=>List Bool) (data p s false) (fun _=>CompareMachine.word count)
def loopHeads (s : State) : Fin 25→Nat:=
  Fin.addCases (m:=24) (n:=1) (motive:=fun _=>Nat) (heads s) (fun _=>1)
def initHeads (out : List Bool) (q : Fin 4) : Fin 25→Nat:=fun i=>
  if i=20 then out.length else if i=18 then (if q=0 then 0 else if q=2 then 2 else 1)
  else if i=19 ∨ i=23 ∨ i=24 then (if q=0 then 0 else 1) else 0
def initData (p : Parameters) (count : Nat) (out : List Bool) (q : Fin 4) : Fin 25→List Bool:=
  Function.update (loopData p (initialState out) count) 18 [false,decide (2≤q.val),false]
def initCfg (p : Parameters) (count : Nat) (out : List Bool) (q : Fin 4) : Configuration 25 4:=
  ⟨q,initHeads out q,initData p count out q⟩

def initMachine : Machine 25 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q _=>if h:q.val<3 then some ⟨⟨q.val+1,by omega⟩,
    fun i=>if i=18 then some (decide (q=1)) else none,
    fun i=>if i=18 then (if q=2 then .left else .right)
      else if q=0 ∧ (i=19 ∨ i=23 ∨ i=24) then .right else .stay⟩ else none

theorem init_step (p : Parameters) (count : Nat) (out : List Bool) (q : Fin 3) :
    step initMachine (initCfg p count out (q.castAdd 1))=some (initCfg p count out ⟨q.val+1,by omega⟩):=by
  fin_cases q
  all_goals
    simp only [step,initMachine,initCfg]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,initHeads,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,initHeads,initData,writeTapeBit]

theorem init_run (p : Parameters) (count : Nat) (out : List Bool) :
    Step initMachine 3 (initHeads out 0) (initData p count out 0)
      (loopHeads (initialState out)) (loopData p (initialState out) count):=by
  have a:=Timed.single (by rfl) (init_step p count out 0)
  have b:=Timed.single (by rfl) (init_step p count out 1)
  have c:=Timed.single (by rfl) (init_step p count out 2)
  obtain ⟨r,hr,rf,_⟩:=((a.trans b).trans c).run (by rfl)
  apply (Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).congr
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
