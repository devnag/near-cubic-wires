import Proof.Packets.CycleCommonReserve

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace Theorem25Completion.CycleWindowScalars

def width (C : Nat):=C+9

theorem capacity (C : Nat) : 512*(C+1)≤2^width C := by
  have h : C+1≤2^C:=Nat.lt_two_pow_self
  unfold width
  rw [pow_add]
  norm_num
  nlinarith only [h]

theorem scalar_guards (C n parent child W : Nat) (hn : n≤C) (hp : parent≤C)
    (hc : child≤C) (hW : W≤64*(C+2)) :
    n<2^width C ∧ min n W+parent<2^width C ∧ 2*child<2^width C ∧ 2*W<2^width C := by
  have h:=capacity C
  have hm:=Nat.min_le_left n W
  omega

theorem reserve_guard (C w : Nat) : 28*width C+35≤CycleCommonReserve.reserve C w := by
  have hp : C+1≤(C+1)^4:=Nat.le_self_pow (by decide) _
  have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
  unfold width CycleCommonReserve.reserve
  nlinarith only [Nat.mul_le_mul hp he,Nat.zero_le C]

end Theorem25Completion.CycleWindowScalars
