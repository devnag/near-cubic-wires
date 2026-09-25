import Proof.Packets.CycleWindowScalars

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open Theorem25Completion

theorem digit_width_guards (M : Nat) :
    M≤2^(Nat.log 2 M+1) ∧ Nat.log 2 M+1≤M+1 ∧ 2^(Nat.log 2 M+1)≤2*(M+1) := by
  refine ⟨(Nat.lt_pow_succ_log_self (by decide : 1<2) M).le,?_,?_⟩
  · have h : Nat.log 2 M≤M:=Nat.log_le_self _ _
    omega
  · by_cases hM:M=0
    · subst M;norm_num
    · have h:=Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hM)
      rw [pow_succ]
      omega

theorem width_from_census (M width w : Nat) (hM : 1 ≤ M)
    (hcount : (M+1)^width ≤ 2^w) : width ≤ w := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  exact (Nat.pow_le_pow_left (by omega : 2 ≤ M+1) width).trans hcount

theorem window_metadata_guards (C w v M W offset target : Nat)
    (hv : v≤C+1) (hM : M≤C) (hW : W≤64*(C+2))
    (ho : offset≤2*C) (ht : target≤2*C) :
    let R:=CycleCommonReserve.reserve C w
    let u:=C+9
    2*u+1≤R ∧ 2*v+1≤R ∧ M+1≤R ∧ 2*W+2≤R ∧
    2*v+2*W+3≤R ∧ offset+2*W<2^u ∧ 2*W+1<2^u ∧ target<2^u := by
  have hp : C+1≤(C+1)^4:=Nat.le_self_pow (by decide) _
  have he : 1≤2^(8*w):=Nat.one_le_two_pow
  have prod:=Nat.mul_le_mul hp he
  have large : 65536*(C+1)≤CycleCommonReserve.reserve C w := by
    unfold CycleCommonReserve.reserve
    nlinarith only [prod]
  have exp:=CycleWindowScalars.capacity C
  change 512*(C+1)≤2^(C+9) at exp
  dsimp only
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
