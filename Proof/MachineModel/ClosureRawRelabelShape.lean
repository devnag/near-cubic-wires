import Proof.CaseAnalysis.FinalSupplierRowInput

/-! The A.12 hardwiring pool keeps the lowered monomials and changes each
absolute child index c to N*yi+c+1. This pins the exact bytes consumed by
NativeFamily.rawWord; no relabelled input tape is assumed. -/
namespace NearCubicWires.P1Closure.RawRelabelShape
open CanonicalFourfoldRowProgram RepairRepresentation SupplierPipeline RepairOrdinary
open RepairSource.CloseoutFinal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def Valid (N : ℕ) (P : StructuralGF2Polynomial) := ∀ m∈P,∀ c∈m,c<N

theorem cache_valid {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (i : Fin gs.length) :
    Valid (ExtDecompositionBatch.GS a gs).length (RepairSource.CloseoutRowsUniversal.cacheAtom a gs i) := by
  unfold RepairSource.CloseoutRowsUniversal.cacheAtom
  rw [CloseoutRowsRawAtomCache.source_getElem]
  exact CloseoutRowsRawAtomMeaning.indices_valid a gs i

end
end NearCubicWires.P1Closure.RawRelabelShape
