import Proof.CaseAnalysis.RowsModeElementary
import Proof.Packets.CycleCommonReserve

/-! The actual binary tuple enumerator fits the physically generated common
reserve, including rejected candidates. Its digit width is the actual source
width; no selected-monomial census is substituted for the full enumeration. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.RepairOrdinary
open Theorem25Completion

theorem elementary_count (v k M : Nat) :
    (CloseoutRowsModeElementary.monomials v k M).length≤2^(v*k) := by
  exact (List.length_filter_le _ _).trans_eq (by simp [RowTupleDigits.candidates])

theorem elementary_budget_polynomial (C v k M : Nat) (hv : v≤ C+1) (hM : M≤ C) :
    CloseoutRowsModeElementary.budget v k M+1≤
      2048*(C+1)^2*(k+1)*2^(v*k) := by
  have hc:=elementary_count v k M
  have hp : 1≤2^(v*k):=Nat.one_le_two_pow
  have vw : v+1≤2*(C+1):=by omega
  have mw : M+1≤ C+1:=by omega
  have prod:=Nat.mul_le_mul vw mw
  have mono : CloseoutRowsModeTupleMonomial.budget v k M+2≤
      64*(C+1)^2*(k+1) := by
    unfold CloseoutRowsModeTupleMonomial.budget CloseoutRowsModeTupleMonomial.loopBudget
      CloseoutRowsModeTupleDigit.budget CloseoutRowsModeIndexBlock.budget
    nlinarith [Nat.mul_le_mul_left k prod,Nat.mul_le_mul_left k hv,
      Nat.mul_le_mul_left k hM,Nat.zero_le (C^2*k)]
  have enum : RowTupleEnumerationReady.budget v k+2≤
      1024*(C+1)^2*(k+1)*2^(v*k) := by
    unfold RowTupleEnumerationReady.budget RowTupleDerivedEnumeration.budget
      RowTupleDerivedEnumeration.metadataTime RowTupleDerivedEnumeration.productTime
      RowTupleLimit.budget RowTupleColdEnumeration.budget RowTupleColdFields.time RowTupleEnumeration.time
    nlinarith [Nat.mul_le_mul_left k hv,Nat.mul_le_mul_left (k*2^(v*k)) hv,
      Nat.mul_le_mul_left ((C+1)^2*(k+1)) hp,Nat.zero_le (C^2*k*2^(v*k))]
  have writer:=Nat.mul_le_mul hc mono
  unfold CloseoutRowsModeElementary.budget CloseoutRowsModeTuplePolynomial.budget
  nlinarith only [enum,writer,Nat.zero_le ((C+1)^2*(k+1)*2^(v*k))]

theorem tuple_exponent (v k width M w : Nat) (hwidth : width≤ w) (hk : k≤ width)
    (hbit : 2^v≤2*(M+1)) (hcount : (M+1)^width≤2^w) : 2^(v*k)≤2^(2*w) := by
  have hc : (M+1)^k≤2^w:=
    (Nat.pow_le_pow_right (by omega : 1≤ M+1) hk).trans hcount
  calc
    2^(v*k)=(2^v)^k:=pow_mul _ _ _
    _≤(2*(M+1))^k:=Nat.pow_le_pow_left hbit _
    _=2^k*(M+1)^k:=mul_pow _ _ _
    _≤2^w*2^w:=Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (hk.trans hwidth)) hc
    _=2^(2*w):=by rw [←pow_add];congr 1;omega

theorem elementary_guard (C v M w width : Nat) (hv : v≤ C+1) (hM : M≤ C)
    (hwidth : width≤ w) (hbit : 2^v≤2*(M+1)) (hcount : (M+1)^width≤2^w) :
    ∀k≤ width,CloseoutRowsModeElementary.budget v k M+1≤ CycleCommonReserve.reserve C w := by
  intro k hk
  have b:=elementary_budget_polynomial C v k M hv hM
  have he:=tuple_exponent v k width M w hwidth hk hbit hcount
  have hkpow : k+1≤2^w:=by have h : w<2^w:=Nat.lt_two_pow_self;omega
  have prod:=Nat.mul_le_mul hkpow he
  have h3 : 2^w*2^(2*w)=2^(3*w):=by rw [←pow_add];congr 1;omega
  rw [h3] at prod
  have h:=Nat.mul_le_mul_left (2048*(C+1)^2) prod
  have exp : 2^(3*w)≤2^(8*w):=Nat.pow_le_pow_right (by decide) (by omega)
  have poly : (C+1)^2≤(C+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have total:=Nat.mul_le_mul poly exp
  unfold CycleCommonReserve.reserve
  nlinarith only [b,h,total,Nat.zero_le ((C+1)^4*2^(8*w))]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
