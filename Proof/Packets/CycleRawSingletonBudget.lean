import Proof.Packets.CycleCommonReserve
import Mathlib.Tactic

/-! Numeric evaluation of the original B=1 raw-substitution envelope. The
cache word is quadratic in the common code width; its degree factor is paid
by the actual width-policy bound, not by an extra power of the code width. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace Theorem25Completion.CycleRawSingletonBudget

def space (cacheLength count degree : Nat) :=
  (128*(cacheLength+count+2)+2)+
    256*(16*(degree*cacheLength+cacheLength+4)^2+(degree*cacheLength+cacheLength+4)+4)
def fuel (cacheLength count degree rows : Nat) := rows*(64*(degree+1)*space cacheLength count degree+2)+3

theorem space_polynomial (C X L count d : Nat) (hX : 1≤X) (hc : count≤C)
    (hL : L≤count*(C+6)) (hd : d+1≤X) :
    space L count d≤262144*(C+1)^4*X^2 := by
  let A:=C+1
  let Y:=A^4*X^2
  have hA : 1≤A:=by dsimp [A];omega
  have hA2 : 1≤A^2:=Nat.one_le_pow _ _ hA
  have hAX : 1≤A^2*X:=Nat.mul_le_mul hA2 hX
  have hYY : 1≤Y:=Nat.mul_le_mul (Nat.one_le_pow _ _ hA) (Nat.one_le_pow _ _ hX)
  have hcount:=Nat.mul_le_mul_right (C+6) hc
  have hL' : L≤3*A^2 := by dsimp [A];nlinarith only [hL,hcount,Nat.zero_le (C^2)]
  have hCX : C+2≤2*A^2 := by dsimp [A];nlinarith only [Nat.zero_le (C^2),Nat.zero_le C]
  have hK : 128*(L+count+2)+2≤1024*A^2 := by nlinarith only [hL',hc,hCX,hA2]
  have hwidth : d*L+L+4≤7*A^2*X := by
    have hh:=Nat.mul_le_mul hd hL'
    nlinarith only [hh,hAX]
  have hwidth2 : (d*L+L+4)^2≤49*Y := by
    have hh:=Nat.pow_le_pow_left hwidth 2
    dsimp only [Y]
    nlinarith only [hh]
  have hAXY : A^2*X≤Y := Nat.mul_le_mul
    (Nat.pow_le_pow_right hA (by decide)) (Nat.le_self_pow (by decide) X)
  have hA2Y : A^2≤Y := (by nlinarith only [Nat.mul_le_mul_left (A^2) hX] : A^2≤A^2*X).trans hAXY
  change space L count d≤262144*A^4*X^2
  rw [Nat.mul_assoc]
  change space L count d≤262144*Y
  unfold space
  nlinarith only [hK,hwidth,hwidth2,hAXY,hA2Y,hYY]

theorem fuel_polynomial (C X L count d rows : Nat) (hX : 1≤X) (hc : count≤C)
    (hL : L≤count*(C+6)) (hd : d+1≤X) (hrows : rows≤X^2) :
    fuel L count d rows≤33554432*(C+1)^4*X^5 := by
  have hs:=space_polynomial C X L count d hX hc hL hd
  have hp:=Nat.mul_le_mul hrows
    (Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 64 hd) hs) 2)
  have hA : 1≤(C+1)^4:=Nat.one_le_pow _ _ (by omega)
  have hX3 : 1≤X^3:=Nat.one_le_pow _ _ hX
  have hX5 : 1≤X^5:=Nat.one_le_pow _ _ hX
  have hZ : 1≤(C+1)^4*X^5:=Nat.mul_le_mul hA hX5
  have hsmall : X^2≤(C+1)^4*X^5 := by
    have h:=Nat.mul_le_mul_left (X^2) (Nat.mul_le_mul hA hX3)
    nlinarith only [h]
  unfold fuel
  nlinarith only [hp,hsmall,hZ]

theorem space_reserve (C w L count d : Nat) (hw : 3≤w) (hc : count≤C)
    (hL : L≤count*(C+6)) (hd : d+1≤2^w) :
    space L count d≤CycleCommonReserve.reserve C w := by
  have h:=space_polynomial C (2^w) L count d (Nat.one_le_pow _ _ (by decide)) hc hL hd
  calc
    _≤262144*(C+1)^4*(2^w)^2:=h
    _=(C+1)^4*2^(18+2*w) := by
      rw [pow_add,←pow_mul,Nat.mul_comm w 2]
      norm_num
      ring
    _≤(C+1)^4*2^(16+8*w):=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
    _=CycleCommonReserve.reserve C w := by
      unfold CycleCommonReserve.reserve
      rw [pow_add]
      norm_num
      ring

theorem fuel_reserve (C w L count d rows : Nat) (hw : 3≤w) (hc : count≤C)
    (hL : L≤count*(C+6)) (hd : d+1≤2^w) (hrows : rows≤2^(2*w)) :
    fuel L count d rows≤CycleCommonReserve.reserve C w := by
  have hr : rows≤(2^w)^2 := by simpa only [←pow_mul,Nat.mul_comm w 2] using hrows
  have h:=fuel_polynomial C (2^w) L count d rows (Nat.one_le_pow _ _ (by decide)) hc hL hd hr
  calc
    _≤33554432*(C+1)^4*(2^w)^5:=h
    _=(C+1)^4*2^(25+5*w) := by
      rw [pow_add,←pow_mul,Nat.mul_comm w 5]
      norm_num
      ring
    _≤(C+1)^4*2^(16+8*w):=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
    _=CycleCommonReserve.reserve C w := by
      unfold CycleCommonReserve.reserve
      rw [pow_add]
      norm_num
      ring

end Theorem25Completion.CycleRawSingletonBudget
