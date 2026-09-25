

import Proof.Packets.PacketsXWalkLiteralMastersGraded
import Proof.Packets.WalkLiteralMastersCost
import Proof.Packets.SourceGradedRankBounds

/-! Canonical rank/depth generation and all palette masters together fit
in65 common reserves for an actual active count bounded by population. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.WalkLiteralMasters
open NearCubicWires NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed.Materializer
open Completion Theorem25Completion.CycleBounds

 theorem graded_capacity_le (C w population active : Nat)
    (hactive : active≤population) (hC : (258*population+2)^2≤C) (hw : 3≤w) :
    SourceGradedRank.capacity population active≤commonReserve C w := by
  have small : 258*population+2≤C :=
    (show 258*population+2≤(258*population+2)^2 from Nat.le_self_pow (by decide) _).trans hC
  have hx : population+active+1≤C+1 := by omega
  have squared:=Nat.pow_le_pow_left hx 2
  have fourth : (C+1)^2≤(C+1)^4 := pow_le_pow_right₀ (by omega : 1≤C+1) (by decide : 2≤4)
  have power : 1024≤2^(8*w) := by
    have p:=pow_le_pow_right₀ (by decide : 1≤(2 : Nat)) (by omega : 10≤8*w)
    norm_num at p ⊢
    exact p
  unfold SourceGradedRank.capacity commonReserve
  have first:=Nat.mul_le_mul_left 67108864 (squared.trans fourth)
  have second:=Nat.mul_le_mul_left (65536*(C+1)^4) power
  nlinarith

end Theorem25Completion.WalkLiteralMasters
