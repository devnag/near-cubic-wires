import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterLayout

/-! Execute one complete original monomial and append its raw substituted body. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine init advance) inner) advance) append) clear
def bodyBudget (R : ℕ) (cs : List Pair) (m : List ℕ) (valid : SubstitutionMonomial.Valid cs m):=
  8+1+1+1+SubstitutionMonomial.budget R cs m valid [[]]+1+1+1+
    SubstitutionAppend.budget (SubstitutionMonomial.value cs m valid [[]])+1+
    (2*(ExtIncidence.stream (SubstitutionMonomial.value cs m valid [[]])).length+2)
structure Fits (C R : ℕ) (cs : List Pair) (m : List ℕ) (valid : SubstitutionMonomial.Valid cs m) : Prop where
  factors : SubstitutionMonomial.Fits C R cs m valid [[]]
  appendTime : CloseoutRowsRawProductRow.budget [] (SubstitutionMonomial.value cs m valid [[]]) ≤ C
  resultLength : (ExtIncidence.stream (SubstitutionMonomial.value cs m valid [[]])).length ≤ C

theorem body_run (C R : ℕ) (cs : List Pair) (m : List ℕ) (valid : SubstitutionMonomial.Valid cs m)
    (pre tail out : List Bool) (hcache : SubstitutionCache.capacity cs ≤ C) (hf : Fits C R cs m valid) :
    Step body (bodyBudget R cs m valid) (heads pre.length out)
      (data C (pre++ExtIncidence.monomialWord m++tail) (cacheWord cs) [] out)
      (heads (pre.length+(ExtIncidence.monomialWord m).length)
        (out++(SubstitutionMonomial.value cs m valid [[]]).flatMap ExtIncidence.monomialWord))
      (data C (pre++ExtIncidence.monomialWord m++tail) (cacheWord cs) []
        (out++(SubstitutionMonomial.value cs m valid [[]]).flatMap ExtIncidence.monomialWord)) := by
  let source:=pre++ExtIncidence.monomialWord m++tail
  let p:=SubstitutionMonomial.value cs m valid [[]]
  have hC : 3 ≤ C:=by unfold SubstitutionCache.capacity at hcache;omega
  have a:=init_run C pre.length source (cacheWord cs) out hC
  have b:=advance_run C pre.length source (cacheWord cs) (ExtIncidence.stream [[]]) out
  have c:=inner_run C R cs m valid (pre++[true]) tail out hcache hf.factors
  have sourceEq : (pre++[true])++m.flatMap ExtIncidence.block++false::tail=source := by
    simp [source,ExtIncidence.monomialWord,List.append_assoc]
  rw [sourceEq] at c
  simp only [List.length_append,List.length_singleton] at c
  have d:=advance_run C (pre.length+1+(m.flatMap ExtIncidence.block).length) source (cacheWord cs) (ExtIncidence.stream p) out
  have e:=append_run C (pre.length+(ExtIncidence.monomialWord m).length) source (cacheWord cs) out p hf.appendTime
  have f:=clear_run C (pre.length+(ExtIncidence.monomialWord m).length) source (cacheWord cs)
    (out++p.flatMap ExtIncidence.monomialWord) p hf.resultLength
  have pos : pre.length+1+(m.flatMap ExtIncidence.block).length+1=pre.length+(ExtIncidence.monomialWord m).length := by
    rw [ExtIncidence.monomialWord_length]
    omega
  rw [pos] at d
  exact ((((a.seq b).seq c).seq d).seq e).seq f

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
