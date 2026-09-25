import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterRun
import Proof.CaseAnalysis.RowsEstimatorSubstitutionMeaning

/-! Exact list equality binds the actual writer to the original raw substitution. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
open CanonicalFourfoldRowProgram
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem value_eq (cs : List Pair) (p : StructuralGF2Polynomial) (valid : Valid cs p) :
    value cs p valid=structuralGF2Substitute (SubstitutionMonomial.atom cs) p := by
  induction p with
  | nil=>rfl
  | cons m p ih=>
    rw [value,SubstitutionMonomial.unit_value,ih]
    rfl

theorem substitute_run (C R : ℕ) (cs : List Pair) (p : StructuralGF2Polynomial) (valid : Valid cs p)
    (pre tail out : List Bool) (hcache : SubstitutionCache.capacity cs ≤ C)
    (hf : ∀ m hm,Fits C R cs m (valid m hm)) :
    Step machine (budget R cs p valid+1+1) (heads pre.length out)
      (data C (pre++ExtIncidence.stream p++tail) (cacheWord cs) [] out)
      (heads (pre.length+(p.flatMap ExtIncidence.monomialWord).length)
        (out++ExtIncidence.stream (structuralGF2Substitute (SubstitutionMonomial.atom cs) p)))
      (data C (pre++ExtIncidence.stream p++tail) (cacheWord cs) []
        (out++ExtIncidence.stream (structuralGF2Substitute (SubstitutionMonomial.atom cs) p))) := by
  simpa only [value_eq] using run C R cs p valid pre tail out hcache hf

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
