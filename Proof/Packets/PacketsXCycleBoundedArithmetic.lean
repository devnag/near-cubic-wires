import Proof.Packets.PacketsXCycleArithmeticCost
import Proof.Packets.PacketsXReusableArithmeticNat

/-! Reusable finite-cost arithmetic on unchanged natural codes. Entry code
fit and the proved intermediate packet census discharge every physical guard. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

def boundedBudget (C w : Nat) := 25*(commonReserve C w+1)

theorem maskNat_width (C : Nat) (P : Ring.Poly Nat) :
    ∀bits∈P.map (maskNat C),bits.length=C := by
  intro bits hb
  obtain ⟨m,_,rfl⟩:=List.mem_map.mp hb
  simp [maskNat]

theorem bounded_guards (C w : Nat) (P Q : Ring.Poly Nat)
    (hp : P.length≤2^w) (hq : Q.length≤2^w) (hw : 1≤w) :
    (∀i,(data C (P.map (maskNat C)) (Q.map (maskNat C)) i).length≤commonReserve C w) ∧
    NormalizedMultiply.budget C (P.map (maskNat C)) (Q.map (maskNat C))+3≤commonReserve C w ∧
    NormalizedAddition.budget C (P.map (maskNat C)) (Q.map (maskNat C))+3≤commonReserve C w := by
  have hp' : (P.map (maskNat C)).length≤2^w := by simpa only [List.length_map] using hp
  have hq' : (Q.map (maskNat C)).length≤2^w := by simpa only [List.length_map] using hq
  exact ⟨arithmetic_input_reserve C w _ _ (maskNat_width C P) (maskNat_width C Q) hp' hq',
    normalized_multiply_reserve C w _ _ (maskNat_width C P) (maskNat_width C Q) hp' hq' hw,
    normalized_addition_reserve C w _ _ (maskNat_width C P) (maskNat_width C Q) hp' hq' hw⟩

theorem bounded_budget_of_guard (C w fuel : Nat) (hcap : fuel+3≤commonReserve C w) :
    budget fuel (commonReserve C w)≤boundedBudget C w := by
  unfold budget boundedBudget
  omega

 theorem nat_mul_bounded (C w : Nat) (P Q : Ring.Poly Nat)
    (hP : Fits C P) (hQ : Fits C Q)
    (hp : P.length≤2^w) (hq : Q.length≤2^w) (hw : 1≤w) :
    Step (machine NormalizedMultiply.machine) (boundedBudget C w)
      heads (natState C (commonReserve C w) P Q)
      heads (natState C (commonReserve C w) P (Ring.mul P Q)) := by
  obtain ⟨hi,hm,ha⟩:=bounded_guards C w P Q hp hq hw
  exact (nat_mul C (commonReserve C w) P Q hP hQ hi hm).enlarge
    (bounded_budget_of_guard C w _ hm)

 theorem nat_add_bounded (C w : Nat) (P Q : Ring.Poly Nat)
    (hP : Fits C P) (hQ : Fits C Q)
    (normalP : Ring.Normal P) (normalQ : Ring.Normal Q)
    (hp : P.length≤2^w) (hq : Q.length≤2^w) (hw : 1≤w) :
    Step (machine NormalizedAddition.machine) (boundedBudget C w)
      heads (natState C (commonReserve C w) P Q)
      heads (natState C (commonReserve C w) P (Ring.add P Q)) := by
  obtain ⟨hi,hm,ha⟩:=bounded_guards C w P Q hp hq hw
  exact (nat_add C (commonReserve C w) P Q hP hQ hi normalP normalQ ha).enlarge
    (bounded_budget_of_guard C w _ ha)

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
