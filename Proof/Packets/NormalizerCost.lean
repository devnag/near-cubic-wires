import Proof.Packets.NormalizerCold

/-! Literal polynomial cost of the complete cold normalizer. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
open NearCubicWires NearCubicWires.RepairSource.ProjectionNormalization

def envelope (B M : Nat) : Nat :=
  128*(M*(2*B+3)+1)^3+2*MaskReverseReady.budget (2*B+3) M+
    4*Normalize.filterCap B M+14

theorem source_length (B : Nat) (raw : List (List Bool))
    (hw : ∀ bits∈raw,bits.length=B) :
    (SuffixScan.stream (Normalize.records raw)).length=raw.length*(2*B+3) := by
  rw [Normalize.source_eq]
  induction raw with
  | nil => simp
  | cons bits raw ih =>
    rw [ParityFilter.candidateStream_cons,List.length_append,List.length_append,
      NearCubicWires.RepairOrdinary.frame_length,
      hw bits (by simp),ih (fun b hb=>hw b (by simp [hb]))]
    simp only [List.length_cons,List.length_nil]
    ring

theorem budget_le (B : Nat) (raw : List (List Bool))
    (hw : ∀ bits∈raw,bits.length=B) : budget B raw≤envelope B raw.length := by
  have hn := (List.dedup_sublist raw).length_le
  have hm := Nat.mul_le_mul_right (6*(2*B+3)+12) hn
  unfold budget Normalize.budget Normalize.prefixBudget DedupMaterialReady.budget envelope
  rw [source_length B raw hw]
  unfold MaskReverseReady.budget at *
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
