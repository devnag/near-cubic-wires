import Proof.Packets.PacketsXWalkTranscriptColumnMeaning
import Proof.Packets.PacketsXMajorityCompleteMeaning

/-! The concrete walk columns satisfy the majority worker's normalized
support and degree invariant, and its result is the frozen walk coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumn
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport VectorBottomUp SubstitutionCensus Theorem25Completion.CycleBounds
noncomputable section
variable {population active depth n : Nat}

theorem coordinate_bounded (C w d root S L : Nat) (mask : Finset (Fin population))
    (wins : Fin depth → Nat) (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) (time : Nat) :
    NormalizedIntermediate.Bounded (Finset.range population) d (coordinate mask wins sample column time) := by
  let seed:=WalkLiteralLoop.seedAt sample time
  let P:=Normalized.structuralListPolynomialVector (canonicalGradedLabel population active) seed wins 0 column
  let atoms:=completedAtoms C population active depth mask seed
  have degree : Ring.Degree d P := Normalized.degree_mono
    (Normalized.degree_structuralListPolynomialVector (canonicalGradedLabel population active) seed wins 0 column) h.degree
  have hb:=SubstitutionCall.result_bounded d (Finset.range population) atoms
    (completed_atoms_bounded C population active depth mask seed) P degree
  have meaning:=LiteralVectorSubstitution.coordinate mask (canonicalGradedLabel population active) seed wins column atoms
    (completed_atoms_meaning C population active depth mask seed h.depthRank h.codeCapacity)
  rw [meaning] at hb
  exact hb

theorem coordinates_bounded (C w d root S L : Nat) (mask : Finset (Fin population))
    (wins : Fin depth → Nat) (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) :
    ∀P∈coordinates mask wins sample column,NormalizedIntermediate.Bounded (Finset.range population) d P := by
  intro P hP
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hP
  exact coordinate_bounded C w d root S L mask wins h sample column i.val

theorem majority_exact (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) :
    MajorityComplete.majority (coordinates mask wins sample column)=
      Normalized.structuralMaskedWalkListCoordinate mask (canonicalGradedLabel population active) wins 0 sample column := by
  exact majority_coordinates mask wins sample column

theorem majority_fits (C w d root S L : Nat) (mask : Finset (Fin population))
    (wins : Fin depth → Nat) (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) (hfit : (population+1)^(d*(n+1))≤2^w) :
    PacketVector.Fits (commonReserve C w)
      ((Normalized.structuralMaskedWalkListCoordinate mask (canonicalGradedLabel population active)
        wins 0 sample column).map (maskNat C)) := by
  have hb:=MajorityComplete.majority_bounded (Finset.range population) d (coordinates mask wins sample column)
    (coordinates_bounded C w d root S L mask wins h sample column)
  rw [majority_exact] at hb
  have hlen : (coordinates mask wins sample column).length=n+1:=List.length_ofFn
  rw [hlen] at hb
  exact VectorBottomUp.packet_fits _ _ (bounded_packet C w (d*(n+1)) (Finset.range population) _ hb
    (by simpa only [Finset.card_range] using hfit)).2

end
end Theorem25Completion.WalkTranscriptColumn
