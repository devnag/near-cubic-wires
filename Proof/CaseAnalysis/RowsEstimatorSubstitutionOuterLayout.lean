import Proof.CaseAnalysis.RowsEstimatorSubstitutionAppend
import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomialRun

/-! A live raw output extends the reusable ten-tape factor bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) (out : List Bool) : Fin 11 → ℕ:=
  Fin.addCases (m:=10) (n:=1) (motive:=fun _=>ℕ) (SubstitutionFactor.heads pos) (fun _=>out.length)
def data (C : ℕ) (source cache acc out : List Bool) : Fin 11 → List Bool:=
  Fin.addCases (m:=10) (n:=1) (motive:=fun _=>List Bool) (SubstitutionFactor.data C source cache [] acc []) (fun _=>out)
def accSlots : Fin 2 → Fin 11:=![3,8]
def appendSlots : Fin 5 → Fin 11:=![5,3,10,7,8]
noncomputable def init:=RecoveryFocus.machine accSlots SubstitutionAppend.unitMachine
noncomputable def inner:=TapeEmbedding.machine 1 SubstitutionMonomial.machine
noncomputable def append:=RecoveryFocus.machine appendSlots SubstitutionAppend.machine
noncomputable def clear:=RecoveryFocus.machine accSlots SubstitutionErase.reset
def advance : Machine 11 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,fun i=>if i=0 then .right else .stay⟩ else none

theorem init_run (C pos : ℕ) (source cache out : List Bool) (hc : 3 ≤ C) :
    Step init 8 (heads pos out) (data C source cache [] out)
      (heads pos out) (data C source cache (ExtIncidence.stream [[]]) out) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionAppend.unit_run C hc)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))

theorem advance_run (C pos : ℕ) (source cache acc out : List Bool) :
    Step advance 1 (heads pos out) (data C source cache acc out)
      (heads (pos+1) out) (data C source cache acc out) := by
  have hs : step advance ⟨0,heads pos out,data C source cache acc out⟩=
      some ⟨1,heads (pos+1) out,data C source cache acc out⟩ := by
    simp only [step,advance,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>simp [applyAction,heads,SubstitutionFactor.heads,Fin.addCases,HeadMove.apply]
    · rfl
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem inner_run (C R : ℕ) (cs : List Pair) (m : List ℕ) (valid : SubstitutionMonomial.Valid cs m)
    (pre tail out : List Bool) (hcache : SubstitutionCache.capacity cs ≤ C)
    (hf : SubstitutionMonomial.Fits C R cs m valid [[]]) :
    Step inner (SubstitutionMonomial.budget R cs m valid [[]]) (heads pre.length out)
      (data C (pre++m.flatMap ExtIncidence.block++false::tail) (cacheWord cs) (ExtIncidence.stream [[]]) out)
      (heads (pre.length+(m.flatMap ExtIncidence.block).length) out)
      (data C (pre++m.flatMap ExtIncidence.block++false::tail) (cacheWord cs)
        (ExtIncidence.stream (SubstitutionMonomial.value cs m valid [[]])) out) :=
  (SubstitutionMonomial.run C R cs m valid pre tail [[]] hcache hf).embed (fun _=>out.length) (fun _=>out)

theorem append_run (C pos : ℕ) (source cache out : List Bool) (acc : List (List ℕ))
    (hc : CloseoutRowsRawProductRow.budget [] acc ≤ C) :
    Step append (SubstitutionAppend.budget acc) (heads pos out) (data C source cache (ExtIncidence.stream acc) out)
      (heads pos (out++acc.flatMap ExtIncidence.monomialWord))
      (data C source cache (ExtIncidence.stream acc) (out++acc.flatMap ExtIncidence.monomialWord)) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionAppend.run C acc out hc)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 2 rfl))

theorem clear_run (C pos : ℕ) (source cache out : List Bool) (acc : List (List ℕ))
    (hc : (ExtIncidence.stream acc).length ≤ C) :
    Step clear (2*(ExtIncidence.stream acc).length+2) (heads pos out) (data C source cache (ExtIncidence.stream acc) out)
      (heads pos out) (data C source cache [] out) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (SubstitutionErase.reset_run C acc hc)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro j;fin_cases j <;>rfl)
  | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
