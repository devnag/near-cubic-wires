import Proof.Packets.NormalizerCost
import Proof.Supplier.SupplierEstimator

/-! The actual cold normalizer retains polynomial cost in its resident raw
bank size. Its exponential factor fits the original preparation load margin. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.SupplierEstimator
open PCJ9eff70d512234a4c_Fixed.Materializer

theorem normalizer_envelope_polynomial (B M : Nat) :
    NormalizeCold.envelope B M≤4096*(M+1)^3*(B+1)^3 := by
  unfold NormalizeCold.envelope MaskReverseReady.budget Normalize.filterCap
    Normalize.probeCap ParityFilter.filterBudget ParityFilter.budget
  nlinarith only [Nat.zero_le (M^3*B^3),Nat.zero_le (M^3*B^2),
    Nat.zero_le (M^3*B),Nat.zero_le (M^3),Nat.zero_le (M^2*B^3),
    Nat.zero_le (M^2*B^2),Nat.zero_le (M^2*B),Nat.zero_le (M^2),
    Nat.zero_le (M*B^3),Nat.zero_le (M*B^2),Nat.zero_le (M*B),
    Nat.zero_le M,Nat.zero_le (B^3),Nat.zero_le (B^2),Nat.zero_le B]

theorem normalizer_budget_polynomial (B : Nat) (raw : List (List Bool))
    (hw : ∀ bits∈raw,bits.length=B) :
    NormalizeCold.budget B raw≤4096*(raw.length+1)^3*(B+1)^3 :=
  (NormalizeCold.budget_le B raw hw).trans (normalizer_envelope_polynomial B raw.length)

end Theorem25Completion.CycleBounds
