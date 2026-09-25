

import Proof.Packets.SourceGradedRank

/-! Exact canonical identification and one fixed polynomial execution/reserve
bound for actual rank generation, independent of the live-set scale. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
namespace Completion.SourceGradedRank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairSource.VerifierDecoding

def capacity (population active : Nat):=67108864*(population+active+1)^2


theorem clog_bound (v : Nat):Nat.clog 2 v≤v:=Nat.clog_le_of_le_pow (Nat.lt_two_pow_self : v < 2^v).le

theorem clog_cost (v : Nat):SourceClog.budget v≤134*(v+1)^2:=by
  have hb:=CloseoutSchedule.Clog.budget_bound v
  have hs:1≤(v+1)^2:=Nat.one_le_pow _ _ (by omega)
  unfold SourceClog.budget
  omega

theorem budget_bound (population active : Nat):budget population active+1≤capacity population active:=by
  let N:=population+active+1
  have hn:1≤N:=by omega
  have hmax:max (256*active) population≤256*N:=by omega
  have hs:256*active+1≤257*N:=by omega
  have ht:max (256*active) population+1≤257*N:=by omega
  have hs2:(256*active+1)^2≤(257*N)^2:=Nat.pow_le_pow_left hs 2
  have ht2:(max (256*active) population+1)^2≤(257*N)^2:=Nat.pow_le_pow_left ht 2
  have hc1:=clog_cost (256*active)
  have hc2:=clog_cost (max (256*active) population)
  have hdepth:depth active≤256*active:=clog_bound _
  have hrank:rank population active ≤ max (256*active) population:=by
    rw [rank,depth,←clog_max]
    exact clog_bound _
  have hscale:UnaryAffine.budget active 256 0≤4096*(active+1):=by
    simp only [UnaryAffine.budget,DimensionPower.cost,WilliamsUnaryProduct.budget,pow_zero,
      Nat.mul_one,Nat.add_zero,Nat.zero_mul]
    omega
  have hn2:N≤N^2:=Nat.le_self_pow (by decide) N
  unfold budget capacity
  change _≤67108864*N^2
  nlinarith

end Completion.SourceGradedRank
