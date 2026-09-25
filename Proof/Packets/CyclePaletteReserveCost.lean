

import Proof.Packets.CyclePaletteReserve

/-! The outer reserve is physically generated within a fixed polynomial
and exponential envelope. All constants are independent of the load parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.ProjectionNormalization
open Completion CyclePaletteReserve

theorem paletteReserve_generation_eq (B w : Nat) :
    CyclePaletteReserve.budget B w=
      6*((B+1)^20*2^(40*w+102))+(640*w+1704)*2^(40*w+102)+
        10*(B+1)^20+10*(B+1)^19+10*(B+1)^18+10*(B+1)^17+10*(B+1)^16+10*(B+1)^15+10*(B+1)^14+10*(B+1)^13+10*(B+1)^12+10*(B+1)^11+10*(B+1)^10+10*(B+1)^9+10*(B+1)^8+10*(B+1)^7+10*(B+1)^6+10*(B+1)^5+10*(B+1)^4+10*(B+1)^3+10*(B+1)^2+10*(B+1)^1+4*B+1524*w+4384 := by
  simp only [CyclePaletteReserve.budget,budget8,budget7,budget6,budget5,budget4,budget3,budget2,budget1,
    cost1,cost2,cost3,cost4,cost5,cost6,cost7,cost8,UnaryAffine.budget,
    DimensionPower.cost,WilliamsUnaryProduct.budget,CloseoutCapacity.Power.budget,
    MatrixScorePower.budget,MatrixUnaryTemplate.budget,exponent,
    pow_zero,Nat.mul_one,←CyclePaletteReserve.value_eq]
  ring

theorem paletteReserve_generation_polynomial (B w : Nat) :
    CyclePaletteReserve.budget B w ≤ 2^116*(B+w+2)^21*2^(40*w) := by
  let X:=B+w+2
  let Y:=2^(40*w+102)
  have hX : 1 ≤ X := by dsimp [X];omega
  have hBX : B+1 ≤ X := by dsimp [X];omega
  have hY : 1 ≤ Y := Nat.one_le_two_pow
  have hp (j : Nat) (hj : j ≤ 21) : (B+1)^j ≤ X^21 :=
    (Nat.pow_le_pow_left hBX j).trans (Nat.pow_le_pow_right hX hj)
  have hx1:=hp 1 (by decide)
  have hx2:=hp 2 (by decide)
  have hx3:=hp 3 (by decide)
  have hx4:=hp 4 (by decide)
  have hx5:=hp 5 (by decide)
  have hx6:=hp 6 (by decide)
  have hx7:=hp 7 (by decide)
  have hx8:=hp 8 (by decide)
  have hx9:=hp 9 (by decide)
  have hx10:=hp 10 (by decide)
  have hx11:=hp 11 (by decide)
  have hx12:=hp 12 (by decide)
  have hx13:=hp 13 (by decide)
  have hx14:=hp 14 (by decide)
  have hx15:=hp 15 (by decide)
  have hx16:=hp 16 (by decide)
  have hx17:=hp 17 (by decide)
  have hx18:=hp 18 (by decide)
  have hx19:=hp 19 (by decide)
  have hx20:=hp 20 (by decide)
  have hw : w ≤ X^21 := (by dsimp [X];omega : w ≤ X).trans (Nat.le_self_pow (by decide) _)
  have hone : 1 ≤ X^21 := Nat.one_le_pow _ _ hX
  simp only [pow_one] at hx1
  have hsmall : 6*(B+1)^20+(640*w+1704)+10*(B+1)^20+10*(B+1)^19+10*(B+1)^18+10*(B+1)^17+10*(B+1)^16+10*(B+1)^15+10*(B+1)^14+10*(B+1)^13+10*(B+1)^12+10*(B+1)^11+10*(B+1)^10+10*(B+1)^9+10*(B+1)^8+10*(B+1)^7+10*(B+1)^6+10*(B+1)^5+10*(B+1)^4+10*(B+1)^3+10*(B+1)^2+10*(B+1)^1+4*B+1524*w+4384 ≤ 8462*X^21 := by
    simp only [pow_one]
    omega
  have hlower : 10*(B+1)^20+10*(B+1)^19+10*(B+1)^18+10*(B+1)^17+10*(B+1)^16+10*(B+1)^15+10*(B+1)^14+10*(B+1)^13+10*(B+1)^12+10*(B+1)^11+10*(B+1)^10+10*(B+1)^9+10*(B+1)^8+10*(B+1)^7+10*(B+1)^6+10*(B+1)^5+10*(B+1)^4+10*(B+1)^3+10*(B+1)^2+10*(B+1)^1+4*B+1524*w+4384 ≤
      (10*(B+1)^20+10*(B+1)^19+10*(B+1)^18+10*(B+1)^17+10*(B+1)^16+10*(B+1)^15+10*(B+1)^14+10*(B+1)^13+10*(B+1)^12+10*(B+1)^11+10*(B+1)^10+10*(B+1)^9+10*(B+1)^8+10*(B+1)^7+10*(B+1)^6+10*(B+1)^5+10*(B+1)^4+10*(B+1)^3+10*(B+1)^2+10*(B+1)^1+4*B+1524*w+4384)*Y := Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ (6*(B+1)^20+(640*w+1704)+10*(B+1)^20+10*(B+1)^19+10*(B+1)^18+10*(B+1)^17+10*(B+1)^16+10*(B+1)^15+10*(B+1)^14+10*(B+1)^13+10*(B+1)^12+10*(B+1)^11+10*(B+1)^10+10*(B+1)^9+10*(B+1)^8+10*(B+1)^7+10*(B+1)^6+10*(B+1)^5+10*(B+1)^4+10*(B+1)^3+10*(B+1)^2+10*(B+1)^1+4*B+1524*w+4384)*Y := by
      rw [paletteReserve_generation_eq]
      dsimp only [Y] at hlower ⊢
      nlinarith only [hlower]
    _ ≤ 8462*X^21*Y := Nat.mul_le_mul_right _ hsmall
    _ ≤ 16384*X^21*Y := by gcongr;norm_num
    _ = _ := by dsimp only [X,Y];rw [pow_add];norm_num;ring

end Theorem25Completion.CycleBounds
