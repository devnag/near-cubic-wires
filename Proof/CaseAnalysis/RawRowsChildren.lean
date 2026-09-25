import Proof.CaseAnalysis.RawRowsModeDegree

/-! The exact existing residual-to-child substitution, specialized to the
corrected ordinary source. Its fresh output supplies the actual child bound. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierPrinter SupplierRadix
open RepairRepresentation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def occurrenceExactChildren
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) : List (ExactThresholdGate q) :=
  (algorithm.output ⟨q, CompilerSemantics.nonStrictAsStrict
      (occurrences.get index).gate⟩).children

/-- Disjointness of the imported decomposition turns its exact-child OR into
linear GF(2) parity. -/
theorem occurrenceExactChildren_parity_eq
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (input : BitInput q) (index : Fin occurrences.length) :
    boolParity
        (fun childIndex :
            Fin (occurrenceExactChildren algorithm occurrences index).length =>
          ((occurrenceExactChildren algorithm occurrences index).get
            childIndex).eval input) =
      (occurrences.get index).eval input := by
  let gate := (occurrences.get index).gate
  let decomposition :=
    algorithm.output ⟨q, CompilerSemantics.nonStrictAsStrict gate⟩
  calc
    boolParity
        (fun childIndex : Fin decomposition.children.length =>
          (decomposition.children.get childIndex).eval input) =
        decomposition.children.any (fun child => child.eval input) :=
      boolParity_finGet_eq_any_of_disjoint decomposition.children
        (fun child => child.eval input) (decomposition.disjoint input)
    _ = (CompilerSemantics.nonStrictAsStrict gate).strictEval input :=
      (decomposition.equivalent input).symm
    _ = gate.eval input :=
      CompilerSemantics.nonStrictAsStrict_eval gate input
    _ = (occurrences.get index).eval input := rfl

theorem actual_children_bound {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (i : Fin gs.length) :
    (occurrenceExactChildren a gs i).length ≤
      a.coefficient*(q+(CompilerSemantics.nonStrictAsStrict (gs.get i).gate).encodingBits+1)^a.degree :=
  RepairOrdinary.DecompositionSource.children_bound a ⟨q,_⟩

end
end NearCubicWires.RepairSource.CloseoutRawRows
