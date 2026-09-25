import Proof.Packets.PacketsXLiteralCache

/-! The whole cold reflected literal cache is charged to additive preparation.
This includes allocation, every actual arithmetic/serialization call, resets,
counted descending control, and the final physical cursor return. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires PCJ9eff70d512234a4c_Fixed.Materializer CycleLiteralPairCost

theorem literal_cache_cost (C w tag count : Nat) (ht : tag≤C) (hc : count≤C) :
    LiteralCacheCold.budget (commonReserve C w) tag count≤128*(C+1)*(commonReserve C w+1) := by
  have hr:=CycleLiteralPairCost.commonReserve_scalar C w
  have hn : count≤commonReserve C w := by omega
  have hn2:=Nat.mul_le_mul_left count hn
  have hnC:=Nat.mul_le_mul_right (commonReserve C w) hc
  unfold LiteralCacheCold.budget LiteralCacheAllocate.budget LiteralPairCache.budget
  nlinarith

theorem literal_cache_polynomial (C w tag count : Nat) (ht : tag≤C) (hc : count≤C) :
    LiteralCacheCold.budget (commonReserve C w) tag count≤16777216*(C+1)^5*2^(8*w) := by
  have h := literal_cache_cost C w tag count ht hc
  have hpower : 1≤(C+1)^4*2^(8*w) := Nat.mul_le_mul
    (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by decide))
  have hR : commonReserve C w+1≤65537*((C+1)^4*2^(8*w)) := by
    unfold commonReserve CycleCommonReserve.reserve
    nlinarith
  calc
    _≤128*(C+1)*(commonReserve C w+1) := h
    _≤128*(C+1)*(65537*((C+1)^4*2^(8*w))) := Nat.mul_le_mul_left _ hR
    _≤16777216*(C+1)^5*2^(8*w) := by
      rw [pow_succ]
      nlinarith [Nat.zero_le ((C+1)*(C+1)^4*2^(8*w))]

end Theorem25Completion.CycleBounds
