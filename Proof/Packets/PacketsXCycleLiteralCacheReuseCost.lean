import Proof.Packets.PacketsXLiteralCacheReuse
import Proof.Packets.PacketsXCycleLiteralCacheCost

/-! Between-level cache replacement is no more expensive than first cold
construction; all clears, reloads and cursor returns are included. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open PCJ9eff70d512234a4c_Fixed.Materializer CycleLiteralPairCost

 theorem literal_cache_reuse_le_cold (R tag count : Nat) :
    LiteralCacheReuse.budget R tag count≤LiteralCacheCold.budget R tag count := by
  unfold LiteralCacheReuse.budget LiteralCacheReload.budget LiteralCacheCold.budget LiteralCacheAllocate.budget
  omega

 theorem literal_cache_reuse_polynomial (C w tag count : Nat) (ht : tag≤C) (hc : count≤C) :
    LiteralCacheReuse.budget (commonReserve C w) tag count≤16777216*(C+1)^5*2^(8*w) :=
  (literal_cache_reuse_le_cold _ tag count).trans (literal_cache_polynomial C w tag count ht hc)

end Theorem25Completion.CycleBounds
