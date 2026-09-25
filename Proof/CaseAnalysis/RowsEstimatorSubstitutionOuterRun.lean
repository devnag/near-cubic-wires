import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterLoop

/-! The actual reusable substitution appends one complete terminated polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finish : Machine 11 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun i=>if i=10 then some false else none,
    fun i=>if i=10 then .right else .stay⟩ else none
noncomputable def machine:=Composition.machine loop finish

theorem finish_run (C pos : ℕ) (source cache out : List Bool) :
    Step finish 1 (heads pos out) (data C source cache [] out)
      (heads pos (out++[false])) (data C source cache [] (out++[false])) := by
  have hs : step finish ⟨0,heads pos out,data C source cache [] out⟩=
      some ⟨1,heads pos (out++[false]),data C source cache [] (out++[false])⟩ := by
    simp only [step,finish,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>simp [applyAction,heads,SubstitutionFactor.heads,Fin.addCases,HeadMove.apply]
    · funext i;fin_cases i <;>simp [applyAction,data,heads,Fin.addCases,Streaming.write_append]
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem loop_run (C R : ℕ) (cs : List Pair) (p : List (List ℕ)) (valid : Valid cs p)
    (pre tail out : List Bool) (hcache : SubstitutionCache.capacity cs ≤ C)
    (hf : ∀ m hm,Fits C R cs m (valid m hm)) :
    Step loop (budget R cs p valid) (heads pre.length out)
      (data C (pre++ExtIncidence.stream p++tail) (cacheWord cs) [] out)
      (heads (pre.length+(p.flatMap ExtIncidence.monomialWord).length)
        (out++(value cs p valid).flatMap ExtIncidence.monomialWord))
      (data C (pre++ExtIncidence.stream p++tail) (cacheWord cs) []
        (out++(value cs p valid).flatMap ExtIncidence.monomialWord)) := by
  obtain ⟨time,ht,tr⟩:=remaining C R cs p valid pre tail out hcache hf
  obtain ⟨r,hr,rf,_⟩:=tr.run (by simp [loop,SubstitutionRepeat.machine,SubstitutionRepeat.final,
    RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel loop time (budget R cs p valid-time) _ r hr
  rw [Nat.add_sub_of_le ht,SubstitutionMonomial.repeat_entry _ 0] at more
  exact Step.of_run more (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem run (C R : ℕ) (cs : List Pair) (p : List (List ℕ)) (valid : Valid cs p)
    (pre tail out : List Bool) (hcache : SubstitutionCache.capacity cs ≤ C)
    (hf : ∀ m hm,Fits C R cs m (valid m hm)) :
    Step machine (budget R cs p valid+1+1) (heads pre.length out)
      (data C (pre++ExtIncidence.stream p++tail) (cacheWord cs) [] out)
      (heads (pre.length+(p.flatMap ExtIncidence.monomialWord).length) (out++ExtIncidence.stream (value cs p valid)))
      (data C (pre++ExtIncidence.stream p++tail) (cacheWord cs) [] (out++ExtIncidence.stream (value cs p valid))) := by
  have first:=loop_run C R cs p valid pre tail out hcache hf
  have last:=finish_run C (pre.length+(p.flatMap ExtIncidence.monomialWord).length)
    (pre++ExtIncidence.stream p++tail) (cacheWord cs) (out++(value cs p valid).flatMap ExtIncidence.monomialWord)
  simpa only [machine,ExtIncidence.stream,List.append_assoc] using first.seq last

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
