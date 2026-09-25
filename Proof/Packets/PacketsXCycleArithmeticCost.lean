import Proof.Packets.PacketsXCycleSerializedCost
import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.NormalizedAdditionData

/-! Actual normalized arithmetic fits the physically generated common reserve.
The hypotheses concern the two resident operand censuses; they apply to every
proved intermediate, including literal-first constructor intermediates. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.RepairSource.ProjectionNormalization
open PCJ9eff70d512234a4c_Fixed.Materializer

theorem product_ready_polynomial (B M N : Nat) :
    MaskProduct.readyBudget B M N≤64*(M*N+M+N+1)*(B+1) := by
  unfold MaskProduct.readyBudget MaskProduct.budget
  nlinarith only [Nat.zero_le (M*N*B),Nat.zero_le (M*N),Nat.zero_le (M*B),
    Nat.zero_le (N*B),Nat.zero_le M,Nat.zero_le N,Nat.zero_le B]

theorem addition_ready_polynomial (B M N : Nat) :
    MaskAddition.budget B M N≤64*(M*N+M+N+1)*(B+1) := by
  unfold MaskAddition.budget
  nlinarith only [Nat.zero_le (M*N*B),Nat.zero_le (M*N),Nat.zero_le (M*B),
    Nat.zero_le (N*B),Nat.zero_le M,Nat.zero_le N,Nat.zero_le B]

theorem operand_census (M N T : Nat) (hM : M≤T) (hN : N≤T) (hT : 2≤T) :
    M*N≤T^2 ∧ M+N≤T^2 ∧ M*N+M+N+1≤2*(T^2+1) := by
  have hp := Nat.mul_le_mul hM hN
  have hs : 2*T≤T^2 := by nlinarith only [hT]
  exact ⟨by nlinarith only [hp],by omega,by nlinarith only [hp,hM,hN,hs]⟩

theorem preparation_allowance (B X : Nat) :
    128*(X+1)*(B+1)+4≤4096*(X+1)^3*(B+1)^3 := by
  nlinarith only [Nat.zero_le (X^3*B^3),Nat.zero_le (X^3*B^2),Nat.zero_le (X^3*B),
    Nat.zero_le (X^3),Nat.zero_le (X^2*B^3),Nat.zero_le (X^2*B^2),Nat.zero_le (X^2*B),
    Nat.zero_le (X^2),Nat.zero_le (X*B^3),Nat.zero_le (X*B^2),Nat.zero_le (X*B),
    Nat.zero_le X,Nat.zero_le (B^3),Nat.zero_le (B^2),Nat.zero_le B]

theorem normalized_multiply_reserve (B w : Nat) (left right : List (List Bool))
    (hl : ∀bits∈left,bits.length=B) (hr : ∀bits∈right,bits.length=B)
    (hleft : left.length≤2^w) (hright : right.length≤2^w) (hw : 1≤w) :
    NormalizedMultiply.budget B left right+3≤commonReserve B w := by
  have hT : 2≤2^w := by simpa using (Nat.pow_le_pow_right (by decide : 1≤2) hw)
  obtain ⟨hmul,_,hcounts⟩:=operand_census left.length right.length (2^w) hleft hright hT
  have hn:=normalizer_budget_polynomial B (MaskProduct.unions left right)
    (NormalizedMultiply.unions_width B left right hl hr)
  rw [MaskProduct.unions_length] at hn
  have hn' : NormalizeCold.budget B (MaskProduct.unions left right)≤
      4096*((2^w)^2+1)^3*(B+1)^3 := hn.trans (by gcongr)
  have hp:=product_ready_polynomial B left.length right.length
  have hp' : MaskProduct.readyBudget B left.length right.length≤128*((2^w)^2+1)*(B+1) := by
    calc
      _≤64*(left.length*right.length+left.length+right.length+1)*(B+1) := hp
      _≤64*(2*((2^w)^2+1))*(B+1) := by gcongr
      _=_ := by ring
  have hpre:=preparation_allowance B ((2^w)^2)
  have whole : NormalizedMultiply.budget B left right+3≤8192*((2^w)^2+1)^3*(B+1)^3 := by
    unfold NormalizedMultiply.budget
    nlinarith only [hn',hp',hpre]
  exact whole.trans (packet_reserve_bound B w ((2^w)^2) (by rw [←pow_mul,Nat.mul_comm w 2]))

theorem normalized_addition_reserve (B w : Nat) (left right : List (List Bool))
    (hl : ∀bits∈left,bits.length=B) (hr : ∀bits∈right,bits.length=B)
    (hleft : left.length≤2^w) (hright : right.length≤2^w) (hw : 1≤w) :
    NormalizedAddition.budget B left right+3≤commonReserve B w := by
  have hT : 2≤2^w := by simpa using (Nat.pow_le_pow_right (by decide : 1≤2) hw)
  obtain ⟨_,hadd,hcounts⟩:=operand_census left.length right.length (2^w) hleft hright hT
  have hn:=normalizer_budget_polynomial B (left.reverse++right)
    (NormalizedAddition.sum_width B left right hl hr)
  simp only [List.length_append,List.length_reverse] at hn
  have hn' : NormalizeCold.budget B (left.reverse++right)≤
      4096*((2^w)^2+1)^3*(B+1)^3 := hn.trans (by gcongr)
  have hp:=addition_ready_polynomial B left.length right.length
  have hp' : MaskAddition.budget B left.length right.length≤128*((2^w)^2+1)*(B+1) := by
    calc
      _≤64*(left.length*right.length+left.length+right.length+1)*(B+1) := hp
      _≤64*(2*((2^w)^2+1))*(B+1) := by gcongr
      _=_ := by ring
  have hpre:=preparation_allowance B ((2^w)^2)
  have whole : NormalizedAddition.budget B left right+3≤8192*((2^w)^2+1)^3*(B+1)^3 := by
    unfold NormalizedAddition.budget
    nlinarith only [hn',hp',hpre]
  exact whole.trans (packet_reserve_bound B w ((2^w)^2) (by rw [←pow_mul,Nat.mul_comm w 2]))

theorem arithmetic_input_lengths (B : Nat) (left right : List (List Bool))
    (hl : ∀bits∈left,bits.length=B) (hr : ∀bits∈right,bits.length=B) :
    ∀i,(NormalizedMultiply.data B left right [] i).length≤
      8*(left.length+right.length+1)*(B+1) := by
  intro i
  fin_cases i <;> simp [NormalizedMultiply.data,NormalizedMultiply.extras,NormalizeCold.data,
    Normalize.records,SuffixScan.stream,NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word,
    NearCubicWires.RepairOrdinary.UnaryTemplate.tape,Fin.addCases,
    MaskProduct.flatten_length B left hl,MaskProduct.flatten_length B right hr]
  all_goals nlinarith only [Nat.zero_le (left.length*B),Nat.zero_le (right.length*B),
    Nat.zero_le left.length,Nat.zero_le right.length,Nat.zero_le B]

theorem arithmetic_input_reserve (B w : Nat) (left right : List (List Bool))
    (hl : ∀bits∈left,bits.length=B) (hr : ∀bits∈right,bits.length=B)
    (hleft : left.length≤2^w) (hright : right.length≤2^w) :
    ∀i,(NormalizedMultiply.data B left right [] i).length≤commonReserve B w := by
  have hT : 1≤2^w := Nat.one_le_two_pow
  have ht2 : 2^w≤(2^w)^2 := Nat.le_self_pow (by decide) _
  have ht3 : (2^w)^2+1≤((2^w)^2+1)^3 := Nat.le_self_pow (by decide) _
  have hb3 : B+1≤(B+1)^3 := Nat.le_self_pow (by decide) _
  have hc : left.length+right.length+1≤2*((2^w)^2+1)^3 := by omega
  intro i
  calc
    _≤8*(left.length+right.length+1)*(B+1) := arithmetic_input_lengths B left right hl hr i
    _≤8*(2*((2^w)^2+1)^3)*(B+1)^3 := by gcongr
    _≤8192*((2^w)^2+1)^3*(B+1)^3 := by nlinarith only [Nat.zero_le (((2^w)^2+1)^3*(B+1)^3)]
    _≤commonReserve B w := packet_reserve_bound B w ((2^w)^2) (by rw [←pow_mul,Nat.mul_comm w 2])

end Theorem25Completion.CycleBounds
