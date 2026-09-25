import Proof.Packets.CycleSubstitutionCost
import Proof.Packets.SubstitutionReusable

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open PCJ9eff70d512234a4c_Fixed.Materializer

 theorem substitution_reusable_polynomial (C w M : Nat) (hM : M≤2^w) :
    SubstitutionCall.totalBudget C (CycleCommonReserve.reserve C w) M≤
      2199023255552*(C+1)^9*2^(17*w) := by
  let T:=(C+1)^9*2^(17*w)
  have hT : 1≤T := Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
    (Nat.one_le_pow _ _ (by decide))
  have hR : CycleCommonReserve.reserve C w≤65536*T := by
    unfold CycleCommonReserve.reserve
    dsimp only [T]
    have hp : (C+1)^4≤(C+1)^9:=Nat.pow_le_pow_right (by omega) (by omega)
    have he : 2^(8*w)≤2^(17*w):=Nat.pow_le_pow_right (by decide) (by omega)
    nlinarith [Nat.mul_le_mul hp he]
  have hCM : (C+1)*M≤T := Nat.mul_le_mul
    (Nat.le_self_pow (by decide) (C+1))
    (hM.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hseek : M*(4*C+6)≤6*T := by nlinarith
  have houter:=substitution_polynomial C w M hM
  have houter' : M*(SubstitutionOuter.bodyBudget C (CycleCommonReserve.reserve C w)+3)+3≤1099511627776*T := by
    simpa only [T,Nat.mul_assoc] using houter
  suffices h : SubstitutionCall.totalBudget C (CycleCommonReserve.reserve C w) M≤2199023255552*T by
    simpa only [T,Nat.mul_assoc] using h
  unfold SubstitutionCall.totalBudget SubstitutionCall.prepareBudget SubstitutionCall.finishBudget
    PhysicalProductSeek.budget SubstitutionOuter.budget
  nlinarith only [houter',hR,hseek,hT]

end Theorem25Completion.CycleBounds
