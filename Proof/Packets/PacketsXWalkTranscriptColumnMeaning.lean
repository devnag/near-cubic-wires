import Proof.Packets.PacketsXWalkTranscriptColumn

/-! The physically extracted increasing-time column has exactly the
original walk-majority constructor, including its literal polynomial order. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptColumn
open NearCubicWires NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierWalk
open PCJ9eff70d512234a4c_Fixed
noncomputable section
variable {population active depth n : Nat}

theorem coordinate_at_time (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) (time : Fin (n+1)) :
    coordinate mask wins sample column time.val=
      Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active)
        (toeplitzWalkEncoding (canonicalGradedRank population active) (sample.vertex time)).1
        wins 0 column := by
  have ht : time.val≤n := by omega
  simp only [coordinate,WalkLiteralLoop.seedAt,WalkTimeLoop.vertex,Nat.min_eq_left ht]

theorem majority_coordinates (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) :
    Normalized.structuralGF2BitMajority
      (fun i : Fin (coordinates mask wins sample column).length=>
        (coordinates mask wins sample column).get i)=
      Normalized.structuralMaskedWalkListCoordinate mask (canonicalGradedLabel population active)
        wins 0 sample column := by
  unfold coordinates
  simp_rw [List.get_ofFn]
  unfold Normalized.structuralMaskedWalkListCoordinate
  congr 1
  · exact List.length_ofFn
  · apply (Fin.heq_fun_iff List.length_ofFn).2
    intro time
    exact coordinate_at_time mask wins sample column ⟨time.val, by simpa using time.isLt⟩

end
end Theorem25Completion.WalkTranscriptColumn
