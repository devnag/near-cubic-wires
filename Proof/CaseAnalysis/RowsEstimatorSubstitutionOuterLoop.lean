import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterBody

/-! Original monomial delimiters control the polynomial substitution loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Valid (cs : List Pair) (p : List (List ℕ)) : Prop:=∀ m∈p,SubstitutionMonomial.Valid cs m
def value (cs : List Pair) : (p : List (List ℕ)) → Valid cs p → List (List ℕ)
  | [],_=>[]
  | m::p,h=>SubstitutionMonomial.value cs m (h m (by simp)) [[]]++value cs p (fun n hn=>h n (by simp [hn]))
def budget (R : ℕ) (cs : List Pair) : (p : List (List ℕ)) → Valid cs p → ℕ
  | [],_=>1
  | m::p,h=>bodyBudget R cs m (h m (by simp))+2+budget R cs p (fun n hn=>h n (by simp [hn]))
noncomputable def loop:=SubstitutionRepeat.machine body 0

theorem remaining (C R : ℕ) (cs : List Pair) (p : List (List ℕ)) (valid : Valid cs p)
    (pre tail out : List Bool) (hcache : SubstitutionCache.capacity cs ≤ C)
    (hf : ∀ m hm,Fits C R cs m (valid m hm)) : ∃ time ≤ budget R cs p valid,Timed loop time
      (SubstitutionRepeat.entry body 0 (heads pre.length out)
        (data C (pre++ExtIncidence.stream p++tail) (cacheWord cs) [] out))
      (SubstitutionRepeat.final body (heads (pre.length+(p.flatMap ExtIncidence.monomialWord).length)
        (out++(value cs p valid).flatMap ExtIncidence.monomialWord))
        (data C (pre++ExtIncidence.stream p++tail) (cacheWord cs) []
          (out++(value cs p valid).flatMap ExtIncidence.monomialWord))) := by
  unfold loop
  induction p generalizing pre out with
  | nil=>
    refine ⟨1,Nat.le_refl _,?_⟩
    simpa [value,ExtIncidence.stream] using SubstitutionRepeat.stop body 0 (heads pre.length out)
      (data C (pre++false::tail) (cacheWord cs) [] out) (by exact Streaming.read_append pre tail false)
  | cons m p ih=>
    let hv:=valid m (by simp)
    let validTail : Valid cs p:=fun n hn=>valid n (by simp [hn])
    let word:=(SubstitutionMonomial.value cs m hv [[]]).flatMap ExtIncidence.monomialWord
    have raw:=body_run C R cs m hv pre (ExtIncidence.stream p++tail) out hcache (hf m (by simp))
    obtain ⟨first,hfirst,tr⟩:=SubstitutionRepeat.body body 0 _ _ _ _ raw
    obtain ⟨rest,hrest,restTrace⟩:=ih validTail (pre++ExtIncidence.monomialWord m) (out++word)
      (fun n hn=>hf n (by simp [hn]))
    have probe:=SubstitutionRepeat.probe body 0 (heads pre.length out)
      (data C (pre++ExtIncidence.monomialWord m++(ExtIncidence.stream p++tail)) (cacheWord cs) [] out) (by
        change readTapeBit (pre++ExtIncidence.monomialWord m++(ExtIncidence.stream p++tail)) pre.length=true
        simp [ExtIncidence.monomialWord,List.append_assoc,Streaming.read_append])
    simp only [List.append_assoc,List.length_append] at tr restTrace probe
    have all:=probe.trans (tr.trans restTrace)
    refine ⟨1+(first+rest),?_,?_⟩
    · change 1+(first+rest) ≤ bodyBudget R cs m hv+2+budget R cs p validTail
      omega
    · simpa only [value,ExtIncidence.stream_cons,List.flatMap_cons,List.flatMap_append,
        List.append_assoc,List.length_append,Nat.add_assoc] using all

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
