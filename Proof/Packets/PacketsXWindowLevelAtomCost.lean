import Proof.Packets.PacketsXWindowLevelAtoms
import Proof.Packets.PacketsXCycleDenseAtomBudget
import Proof.Packets.PacketsXCycleLiteralCacheReuseCost

/-! All physical literal-cache construction and dense-table preparation
costs are paid by the unchanged common reserve envelope. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open Theorem25Completion Theorem25Completion.CycleBounds

theorem level_atoms_budget (C w tag count : Nat) (ht : tag≤C) (hc : count≤C) :
    levelAtomsBudget C (commonReserve C w) tag count≤2^28*(C+1)^6*2^(8*w) := by
  have h5 : (C+1)^5≤(C+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : (C+1)^4≤(C+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpow : 1≤(C+1)^6 := Nat.one_le_pow _ _ (by omega)
  have hexp : 1≤2^(8*w) := Nat.one_le_pow _ _ (by decide)
  have hprod : 1≤(C+1)^6*2^(8*w) := by simpa using Nat.mul_le_mul hpow hexp
  have hcache:=literal_cache_reuse_polynomial C w tag count ht hc
  have reserveEq : CycleLiteralPairCost.commonReserve C w=commonReserve C w := rfl
  rw [reserveEq] at hcache
  have hcache' : LiteralCacheReuse.budget (commonReserve C w) tag count≤16777216*(C+1)^6*2^(8*w) :=
    hcache.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16777216 h5))
  have hdense:=CycleDenseAtomCost.cold_budget_polynomial C w count hc
  have hreserve : commonReserve C w≤65536*(C+1)^6*2^(8*w) := by
    unfold commonReserve
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 65536 h4)
  unfold levelAtomsBudget LiteralCacheTransaction.budget DenseAtomBoundary.budget
  norm_num at hdense ⊢
  nlinarith only [hcache',hdense,hreserve,hprod,
    Nat.zero_le (C*(12*commonReserve C w+24))]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
