import Proof.CaseAnalysis.RowsEstimatorSubstitutionTime

/-! No prefix-fit premise remains in the bounded actual substitution consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
open CanonicalFourfoldRowProgram CloseoutRowsRawPairSeek LocalBitMultitape ExtDecompositionBatch
open SubstitutionOuter (heads data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fuel (cs : List Pair) (B d rows : ℕ):=
  rows*(64*(d+1)*space cs B d (cacheWord cs).length+2)+3

theorem bounded_run (cs : List Pair) (B d : ℕ) (hB : 1 ≤ B)
    (hc : ∀ i (hi : i<cs.length),(cs[i].1++cs[i].2).length ≤ B)
    (p : StructuralGF2Polynomial) (valid : SubstitutionOuter.Valid cs p)
    (hd : ∀ m∈p,m.length ≤ d) (pre tail out : List Bool) :
    SubstitutionOuter.budget (rowCapacity (widthBound d (cacheWord cs).length)) cs p valid+1+1 ≤ fuel cs B d p.length ∧
    Step SubstitutionOuter.machine
      (SubstitutionOuter.budget (rowCapacity (widthBound d (cacheWord cs).length)) cs p valid+1+1)
      (heads pre.length out)
      (data (space cs B d (cacheWord cs).length) (pre++ExtIncidence.stream p++tail) (cacheWord cs) [] out)
      (heads (pre.length+(p.flatMap ExtIncidence.monomialWord).length)
        (out++ExtIncidence.stream (structuralGF2Substitute (SubstitutionMonomial.atom cs) p)))
      (data (space cs B d (cacheWord cs).length) (pre++ExtIncidence.stream p++tail) (cacheWord cs) []
        (out++ExtIncidence.stream (structuralGF2Substitute (SubstitutionMonomial.atom cs) p))) := by
  have hcache : SubstitutionCache.capacity cs ≤ space cs B d (cacheWord cs).length:=by
    unfold space capacity;omega
  have hf:=fun m hm=>monomial_fits cs B d hB hc m (valid m hm) (hd m hm)
  constructor
  · have h:=outer_time _ _ d cs p valid hcache hf hd
    unfold fuel
    omega
  · exact SubstitutionOuter.substitute_run _ _ cs p valid pre tail out hcache hf

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
