import Proof.Packets.CycleCommonReserve
import Proof.Packets.SubstitutionOuterStep
import Proof.Supplier.SupplierEstimator

/-! The actual nested substitution controller is paid as additive preparation.
Its two reserve factors and actual outer polynomial census contribute 17w;
common code-width contributes nine powers and therefore at most 9K. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open PCJ9eff70d512234a4c_Fixed.Materializer

theorem substitution_polynomial (C w M : Nat) (hM : M≤2^w) :
    M*(SubstitutionOuter.bodyBudget C (CycleCommonReserve.reserve C w)+3)+3≤
      1099511627776*(C+1)^9*2^(17*w) := by
  let X:=(C+1)^4*2^(8*w)
  have hX : 1≤X := Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
    (Nat.one_le_pow _ _ (by decide))
  have hR : CycleCommonReserve.reserve C w+1≤65537*X := by
    dsimp only [CycleCommonReserve.reserve,X]
    dsimp only [X] at hX
    nlinarith
  have ht : 1≤2^w := Nat.one_le_pow _ _ (by decide)
  have hZ : 1≤(C+1)*X^2 := Nat.mul_le_mul (show 1≤C+1 by omega) (Nat.one_le_pow 2 X hX)
  have bound : M*(SubstitutionOuter.bodyBudget C (CycleCommonReserve.reserve C w)+3)+3≤
      (200*65537^2+6)*((C+1)*X^2)*2^w := by
    have hsq:=Nat.pow_le_pow_left hR 2
    have hbody : SubstitutionOuter.bodyBudget C (CycleCommonReserve.reserve C w)≤
        200*65537^2*((C+1)*X^2) := by
      unfold SubstitutionOuter.bodyBudget
      nlinarith [Nat.mul_le_mul_left (200*(C+1)) hsq]
    have hmul:=Nat.mul_le_mul hM (Nat.add_le_add_right hbody 3)
    have hZT:=Nat.mul_le_mul hZ ht
    have hZT2:=Nat.mul_le_mul_right (2^w) hZ
    nlinarith
  calc
    _≤(200*65537^2+6)*((C+1)*X^2)*2^w := bound
    _≤1099511627776*((C+1)*X^2)*2^w := by gcongr;norm_num
    _=_ := by
      dsimp only [X]
      rw [mul_pow,←pow_mul,←pow_mul]
      have hp : 8*w*2+w=17*w := by omega
      rw [show (4:Nat)*2=8 by decide]
      calc
        _=1099511627776*(C+1)^9*(2^(8*w*2)*2^w) := by ring
        _=_ := by rw [←pow_add,hp]

end Theorem25Completion.CycleBounds
