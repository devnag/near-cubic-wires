

import Proof.Packets.CycleCommonReserve
import Proof.Supplier.SupplierEstimator

/-! Charge the physically generated reset capacity to the same additive
preparation envelope. The reserve-generation machine is not a free oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.ProjectionNormalization
open Completion CycleCommonReserve

theorem commonReserve_generation_eq (B w : Nat) :
    CycleCommonReserve.budget B w=
      6*((B+1)^4*2^(8*w+16))+(128*w+328)*2^(8*w+16)+
        10*(B+1)^4+10*(B+1)^3+10*(B+1)^2+10*(B+1)+4*B+308*w+920 := by
  simp only [CycleCommonReserve.budget,budget8,budget7,budget6,budget5,budget4,budget3,budget2,budget1,
    cost1,cost2,cost3,cost4,cost5,cost6,cost7,cost8,UnaryAffine.budget,
    DimensionPower.cost,WilliamsUnaryProduct.budget,CloseoutCapacity.Power.budget,
    MatrixScorePower.budget,MatrixUnaryTemplate.budget,exponent,
    pow_zero,Nat.mul_one,←CycleCommonReserve.value_eq]
  ring

theorem commonReserve_generation_polynomial (B w : Nat) :
    CycleCommonReserve.budget B w≤134217728*(B+w+2)^5*2^(8*w) := by
  let X := B+w+2
  let Y := 2^(8*w+16)
  have hX : 1≤X := by dsimp [X];omega
  have hBX : B+1≤X := by dsimp [X];omega
  have hY : 1≤Y := Nat.one_le_two_pow
  have hx4 : (B+1)^4≤X^5 :=
    (Nat.pow_le_pow_left hBX 4).trans (Nat.pow_le_pow_right hX (by decide))
  have hx3 : (B+1)^3≤X^5 :=
    (Nat.pow_le_pow_left hBX 3).trans (Nat.pow_le_pow_right hX (by decide))
  have hx2 : (B+1)^2≤X^5 :=
    (Nat.pow_le_pow_left hBX 2).trans (Nat.pow_le_pow_right hX (by decide))
  have hx1 : B+1≤X^5 := hBX.trans (Nat.le_self_pow (by decide) _)
  have hw : w≤X^5 := (by dsimp [X];omega : w≤X).trans (Nat.le_self_pow (by decide) _)
  have hone : 1≤X^5 := Nat.one_le_pow _ _ hX
  have hsmall :
      6*(B+1)^4+(128*w+328)+10*(B+1)^4+10*(B+1)^3+
        10*(B+1)^2+10*(B+1)+4*B+308*w+920≤1734*X^5 := by omega
  have hlower :
      10*(B+1)^4+10*(B+1)^3+10*(B+1)^2+10*(B+1)+4*B+308*w+920≤
        (10*(B+1)^4+10*(B+1)^3+10*(B+1)^2+10*(B+1)+4*B+308*w+920)*Y :=
    Nat.le_mul_of_pos_right _ (by omega)
  calc
    _≤(6*(B+1)^4+(128*w+328)+10*(B+1)^4+10*(B+1)^3+
        10*(B+1)^2+10*(B+1)+4*B+308*w+920)*Y := by
      rw [commonReserve_generation_eq]
      dsimp only [Y] at hlower ⊢
      nlinarith only [hlower]
    _≤1734*X^5*Y := Nat.mul_le_mul_right _ hsmall
    _≤2048*X^5*Y := by gcongr;norm_num
    _=_ := by dsimp only [X,Y];rw [pow_add];norm_num;ring

end Theorem25Completion.CycleBounds
