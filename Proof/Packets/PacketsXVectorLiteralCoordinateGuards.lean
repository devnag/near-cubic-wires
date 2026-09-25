import Proof.Packets.PacketsXVectorLiteralCoordinate

/-! Capacity and census bounds for each actual whole-coordinate call,
including its retained left operand and its exact substituted answer. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.RepairSource.CloseoutRawRows
open NormalizedFiniteTransport SubstitutionCensus Theorem25Completion.CycleBounds
noncomputable section

theorem literal_coordinate_guards (C w d population active depth : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat) (candidate : Fin (population+1))
    (hd : depth≤canonicalGradedRank population active) (hC : (depth+2*population+2)^2≤C)
    (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population+1)^d≤2^w) (hliteral : (population*(2*depth+1)+2)^d≤2^w) :
    let P:=Normalized.structuralListPolynomialVector (canonicalGradedLabel population active) seed wins 0 candidate
    let atoms:=completedAtoms C population active depth mask seed
    let answer:=Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active) seed wins 0 candidate
    P.length≤2^w ∧ VectorAccumulator.Fits (commonReserve C w) (P.map (maskNat C)) ∧
      VectorAccumulator.Fits (commonReserve C w) ((SubstitutionCall.leftResult atoms P []).map (maskNat C)) ∧
      VectorAccumulator.Fits (commonReserve C w) (answer.map (maskNat C)) := by
  dsimp only
  let P:=Normalized.structuralListPolynomialVector (canonicalGradedLabel population active) seed wins 0 candidate
  let atoms:=completedAtoms C population active depth mask seed
  have degree : Ring.Degree d P := Normalized.degree_mono
    (Normalized.degree_structuralListPolynomialVector (canonicalGradedLabel population active) seed wins 0 candidate) hdegree
  have count : P.length≤2^w :=
    (LiteralAlphabet.size_le (LiteralAlphabet.good_vectorFrom (canonicalGradedLabel population active) seed wins 0 0 candidate) degree).trans hliteral
  have ha:=completed_atoms_bounded C population active depth mask seed
  have fit : ((Finset.range population).card+1)^d≤2^w := by simpa only [Finset.card_range] using hfit
  have lc:=SubstitutionCall.leftResult_count w d (Finset.range population) fit atoms ha P degree [] (by simp)
  have rb:=SubstitutionCall.result_bounded d (Finset.range population) atoms ha P degree
  have meaning:=LiteralVectorSubstitution.coordinate mask (canonicalGradedLabel population active) seed wins candidate atoms
    (completed_atoms_meaning C population active depth mask seed hd hC)
  rw [meaning] at rb
  exact ⟨count,(SubstitutionCensus.packet_fits C w _ (mask_width C P) (by simpa only [List.length_map] using count)).2,
    (SubstitutionCensus.packet_fits C w _ (mask_width C _) (by simpa only [List.length_map] using lc)).2,
    (bounded_packet C w d (Finset.range population) _ rb fit).2⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
