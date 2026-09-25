

import Proof.Packets.PacketsXWalkLiteralProgram
import Proof.Packets.WalkLiteralExecutionCost

/-! Cost of the actual walk program, including its initially empty scratch
and transcript allocation, all visits, and the paid transcript rewind. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierToeplitzCore
open NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer VectorBottomUp

theorem literal_zero_rectangle_cost (C w M n : Nat) (hM : M≤C) :
    PhysicalZeroRectangle.budget (commonReserve C w) (M+1) n≤
      (n+1)*(2^24*literalWorkScale C w) := by
  let B:=literalWorkScale C w
  let R:=commonReserve C w
  have hb : 1≤B:=literal_work_positive C w
  have hrow : (M+1)*(R+1)≤131072*B:=literal_work_row C w M hM
  have per : (M+1)*(12*R+24)+20≤2^24*B := by
    norm_num
    nlinarith only [hrow,hb]
  have many:=Nat.mul_le_mul_left (n+1) per
  unfold PhysicalZeroRectangle.budget PhysicalZeroRectangle.appendFuel
    PhysicalZeroRectangle.rewindFuel PhysicalZeroRectangle.rowFuel PhysicalZeroRectangle.backFuel
  change n*((M+1)*(8*R+14)+3+3)+4+((M+1)*(8*R+14)+3)+1+
    (n*((M+1)*(4*R+10)+7+3)+4+((M+1)*(4*R+10)+7))≤(n+1)*(2^24*B)
  nlinarith only [many]

attribute [local irreducible] commonReserve paletteReserve

theorem literal_cold_walk_cost (C w M active root depth n : Nat) (hw : 3≤w)
    (hM : M≤C) (hd : depth≤C) (hroot : root≤commonReserve C w)
    (hrank : canonicalGradedRank M active≤9*M) :
    WalkLiteralCold.programBudget C w M active root depth (paletteReserve C w) n≤
      (n+1)*(2^111*literalWorkScale C w) := by
  let B:=literalWorkScale C w
  let R:=commonReserve C w
  let S:=paletteReserve C w
  have hb : 1≤B:=literal_work_positive C w
  have hm : M+1≤B:=literal_work_population C w M hM
  have hrow : (M+1)*(R+1)≤131072*B:=literal_work_row C w M hM
  have hR : R≤131072*B := by nlinarith only [hrow]
  have hs : S=2^102*B := by unfold S paletteReserve B literalWorkScale;ring
  have allocation:=literal_zero_rectangle_cost C w M n hM
  have execution:=literal_collected_walk_cost C w M active root depth n hw hM hd hroot hrank
  change _≤(n+1)*(2^24*B) at allocation
  change _≤(n+1)*(2^109*B) at execution
  have overhead : 2*R+2*S+2*M+18≤2^104*B := by
    norm_num at hs ⊢
    omega
  have overonce : 2*R+2*S+2*M+18≤(n+1)*(2^104*B) := by
    exact overhead.trans (Nat.le_mul_of_pos_left _ (by omega))
  unfold WalkLiteralCold.programBudget WalkLiteralCold.budget
    WalkLiteralCold.prepareBudget WalkLiteralCold.paletteBudget
  change 2*R+7+(2*S+2*M+9+1+PhysicalZeroRectangle.budget R (M+1) n+1+
    WalkTranscriptRewind.collectedBudget C w M active root depth S n)≤(n+1)*(2^111*B)
  norm_num at allocation execution overonce ⊢
  nlinarith only [allocation,execution,overonce]

end Theorem25Completion.CycleBounds
