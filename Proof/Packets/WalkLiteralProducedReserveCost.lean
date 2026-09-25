

import Proof.Packets.PacketsXWalkLiteralProducedReserveRun
import Proof.Packets.WalkLiteralProducedCost
import Proof.Packets.CycleCommonReserveCost
import Proof.Packets.CyclePaletteReserveCost

/-! Paid generation of both reserves and the literal sample walk, in the
caller's raw dimension variables. The coefficient is fixed before requests. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierToeplitzCore
open NearCubicWires.CanonicalFourfoldRowProgram Completion
open PCJ9eff70d512234a4c_Fixed.Materializer VectorBottomUp

attribute [local irreducible] commonReserve paletteReserve

theorem literal_produced_reserve_cost (C w M active root depth n : Nat) (mask : List Bool)
    (hw : 3≤w) (hM : M≤C) (hd : depth≤C) (hroot : root≤commonReserve C w)
    (hrank : canonicalGradedRank M active≤9*M)
    (hgraded : WalkLiteralMasters.gradedBudget C (commonReserve C w) root M active mask≤
      65*commonReserve C w) :
    WalkLiteralProducedReserve.budget C w root M active depth n mask≤
      (n+1)*(2^118*((C+w+2)^21*2^(40*w))) := by
  let X:=(C+w+2)^21*2^(40*w)
  have hbase : 1≤C+w+2 := by omega
  have hpow : 1≤2^(40*w):=Nat.one_le_two_pow
  have hx : 1≤X := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (Nat.one_le_pow 21 _ hbase) hpow
  have hlin : C+w+2≤X :=
    (Nat.le_self_pow (by decide) _).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hc : (C+1)^20≤(C+w+2)^21 :=
    (Nat.pow_le_pow_left (by omega : C+1≤C+w+2) 20).trans
      (Nat.pow_le_pow_right hbase (by decide))
  have hb : literalWorkScale C w≤X := Nat.mul_le_mul_right _ hc
  have hfive : (C+w+2)^5*2^(8*w)≤X :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hbase (by decide))
      (Nat.pow_le_pow_right (by decide) (by omega))
  have common := commonReserve_generation_polynomial C w
  rw [Nat.mul_assoc] at common
  have common' := common.trans (Nat.mul_le_mul_left 134217728 hfive)
  have palette := paletteReserve_generation_polynomial C w
  rw [Nat.mul_assoc] at palette
  change _≤2^116*X at palette
  have produced := (literal_produced_walk_cost C w M active root depth n mask
    hw hM hd hroot hrank hgraded).trans
      (Nat.mul_le_mul_left (n+1) (Nat.mul_le_mul_left (2^112) hb))
  have setup : WalkLiteralProducedReserve.setupBudget C w+1≤2^117*X := by
    unfold WalkLiteralProducedReserve.setupBudget
    norm_num at palette ⊢
    omega
  have setup_many := setup.trans (Nat.le_mul_of_pos_left _ (by omega : 0<n+1))
  have hs : WalkLiteralProducedReserve.S C w=paletteReserve C w := by
    unfold WalkLiteralProducedReserve.S CyclePaletteReserve.reserve paletteReserve
    rfl
  unfold WalkLiteralProducedReserve.budget
  rw [hs]
  change WalkLiteralProducedReserve.setupBudget C w+1+
    WalkLiteralProduced.budget C w root M active depth (paletteReserve C w) n mask≤
      (n+1)*(2^118*X)
  norm_num at produced setup_many ⊢
  nlinarith only [produced,setup_many]

end Theorem25Completion.CycleBounds
