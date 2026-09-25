

import Proof.Packets.PacketsXWalkLiteralProducedRun
import Proof.Packets.WalkLiteralCost
import Proof.Packets.WalkLiteralMastersGradedCost

/-! The raw-master producer, all paid copies and the complete cold walk
remain within the same fixed alphabet/width cost class. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierToeplitzCore
open NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer VectorBottomUp

attribute [local irreducible] commonReserve paletteReserve

theorem literal_produced_walk_cost (C w M active root depth n : Nat) (mask : List Bool)
    (hw : 3≤w) (hM : M≤C) (hd : depth≤C) (hroot : root≤commonReserve C w)
    (hrank : canonicalGradedRank M active≤9*M)
    (hgraded : WalkLiteralMasters.gradedBudget C (commonReserve C w) root M active mask≤
      65*commonReserve C w) :
    WalkLiteralProduced.budget C w root M active depth (paletteReserve C w) n mask≤
      (n+1)*(2^112*literalWorkScale C w) := by
  let B:=literalWorkScale C w
  let R:=commonReserve C w
  have hb : 1≤B:=literal_work_positive C w
  have hrow : (M+1)*(R+1)≤131072*B:=literal_work_row C w M hM
  have hR : R≤131072*B := by nlinarith only [hrow]
  have cold:=literal_cold_walk_cost C w M active root depth n hw hM hd hroot hrank
  change _≤(n+1)*(2^111*B) at cold
  have prep : WalkLiteralProduced.entryBudget C R root M active mask+1≤2^24*B := by
    unfold WalkLiteralProduced.entryBudget
    change _≤65*R at hgraded
    norm_num
    dsimp only [R] at hgraded ⊢
    omega
  have prepmany := prep.trans (Nat.le_mul_of_pos_left (2^24*B) (by omega : 0<n+1))
  unfold WalkLiteralProduced.budget
  change WalkLiteralProduced.entryBudget C R root M active mask+1+_≤(n+1)*(2^112*B)
  norm_num at cold prepmany ⊢
  nlinarith only [cold,prepmany]

end Theorem25Completion.CycleBounds
