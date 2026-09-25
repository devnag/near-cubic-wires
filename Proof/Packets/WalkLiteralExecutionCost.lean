

import Proof.Packets.PacketsXWalkTranscriptRewindJoined
import Proof.Packets.WalkTranscriptRewindCost
import Proof.Packets.PacketsXVectorLiteralPaletteCost
import Proof.Packets.PhysicalZeroRectangle

/-! A fixed polynomial-times-exponential envelope for the actual walk
transcript producer, including its paid return to the first packet. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierToeplitzCore
open NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer VectorBottomUp

def literalWorkScale (C w : Nat) := (C+1)^20*2^(40*w)

theorem literal_work_positive (C w : Nat) : 1≤literalWorkScale C w := by
  exact Nat.mul_pos (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by decide))

theorem literal_work_population (C w M : Nat) (hM : M≤C) : M+1≤literalWorkScale C w := by
  have hp : C+1≤(C+1)^20 := Nat.le_self_pow (by decide) _
  have he : 1≤2^(40*w) := Nat.one_le_pow _ _ (by decide)
  exact (Nat.add_le_add_right hM 1).trans (hp.trans (by
    simpa only [Nat.mul_one,literalWorkScale] using Nat.mul_le_mul_left ((C+1)^20) he))

theorem literal_work_row (C w M : Nat) (hM : M≤C) :
    (M+1)*(commonReserve C w+1)≤131072*literalWorkScale C w := by
  let B:=literalWorkScale C w
  have hCB : C+1≤B:=literal_work_population C w C le_rfl
  have hpow : (C+1)^5*2^(8*w)≤B := by
    exact Nat.mul_le_mul
      (Nat.pow_le_pow_right (by omega : 1≤C+1) (by decide : 5≤20))
      (Nat.pow_le_pow_right (by decide) (by omega : 8*w≤40*w))
  have main : (C+1)*commonReserve C w≤65536*B := by
    unfold commonReserve
    have he : (C+1)*(65536*(C+1)^4*2^(8*w))=65536*((C+1)^5*2^(8*w)) := by ring
    rw [he]
    exact Nat.mul_le_mul_left _ hpow
  have first:=Nat.mul_le_mul_right (commonReserve C w+1) (Nat.add_le_add_right hM 1)
  change _≤131072*B
  nlinarith only [first,main,hCB]

attribute [local irreducible] commonReserve paletteReserve

theorem literal_visit_cost (C w M active root depth : Nat) (hw : 3≤w)
    (hM : M≤C) (hd : depth≤C) (hroot : root≤commonReserve C w)
    (hrank : canonicalGradedRank M active≤9*M) :
    WalkLiteralLoop.visitFuel C w M active root depth (paletteReserve C w)≤
      2^106*literalWorkScale C w := by
  let B:=literalWorkScale C w
  let R:=commonReserve C w
  let S:=paletteReserve C w
  have hb : 1≤B:=literal_work_positive C w
  have hm : M+1≤B:=literal_work_population C w M hM
  have hrow : (M+1)*(R+1)≤131072*B:=literal_work_row C w M hM
  have hR : R≤131072*B := by nlinarith only [hrow]
  have hr : canonicalGradedRank M active≤9*B := by omega
  have hp : literalPaletteFuel C w M root depth S≤2^104*B := by
    calc
      literalPaletteFuel C w M root depth S≤2^104*(C+1)^20*2^(40*w) :=
        literal_palette_program_cost C w M root depth hw hM hd hroot
      _=2^104*B := by unfold B literalWorkScale;ring
  have hs : S=2^102*B := by unfold S paletteReserve B literalWorkScale;ring
  have ha : PacketVectorAppend.budget R (M+1)≤7340043*B := by
    unfold PacketVectorAppend.budget
    nlinarith only [hrow,hb]
  unfold WalkLiteralLoop.visitFuel WalkLiteralVisit.budget WalkPaletteSeedReady.budget
    literalPaletteRefreshCollectFuel literalPaletteRefreshFuel
  change 28*canonicalGradedRank M active+8*R+61+1+
    (2*S+7+literalPaletteFuel C w M root depth S+1+PacketVectorAppend.budget R (M+1))≤2^106*B
  norm_num at hp hs ⊢
  omega

theorem literal_advance_cost (C w M active : Nat) (hM : M≤C)
    (hrank : canonicalGradedRank M active≤9*M) :
    WalkLiteralAdvance.budget (canonicalGradedRank M active) (commonReserve C w)≤
      2^26*literalWorkScale C w := by
  let B:=literalWorkScale C w
  have hb : 1≤B:=literal_work_positive C w
  have hm : M+1≤B:=literal_work_population C w M hM
  have hrow:=literal_work_row C w M hM
  change (M+1)*(commonReserve C w+1)≤131072*B at hrow
  have hR : commonReserve C w≤131072*B := by nlinarith only [hrow]
  have hr : canonicalGradedRank M active≤9*B := by omega
  have side:=twice_toeplitzWalkSideBits_le (canonicalGradedRank M active)
  have bits:=toeplitzSeedBits_le_three_mul (canonicalGradedRank M active)
  unfold WalkLiteralAdvance.budget
  change _≤2^26*B
  norm_num
  omega

theorem literal_collected_walk_cost (C w M active root depth n : Nat) (hw : 3≤w)
    (hM : M≤C) (hd : depth≤C) (hroot : root≤commonReserve C w)
    (hrank : canonicalGradedRank M active≤9*M) :
    WalkTranscriptRewind.collectedBudget C w M active root depth (paletteReserve C w) n≤
      (n+1)*(2^109*literalWorkScale C w) := by
  let B:=literalWorkScale C w
  have hb : 1≤B:=literal_work_positive C w
  have hv:=literal_visit_cost C w M active root depth hw hM hd hroot hrank
  have ha:=literal_advance_cost C w M active hM hrank
  change _≤2^106*B at hv
  change _≤2^26*B at ha
  have hrow:=literal_work_row C w M hM
  change (M+1)*(commonReserve C w+1)≤131072*B at hrow
  have back:=WalkTranscriptRewind.budget_le (commonReserve C w) (M+1) n (by omega)
  have per : (M+1)*(4*commonReserve C w+20)≤2621440*B := by nlinarith only [hrow]
  have hback : WalkTranscriptRewind.budget (commonReserve C w) (M+1) n≤
      (n+1)*(2621440*B)+1 := by
    exact back.trans (by simpa only [Nat.mul_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) per) 1)
  have hbody : WalkLiteralLoop.bodyFuel C w M active root depth (paletteReserve C w)+3≤2^107*B := by
    unfold WalkLiteralLoop.bodyFuel
    norm_num at hv ha ⊢
    omega
  have repeated:=Nat.mul_le_mul_left n hbody
  unfold WalkTranscriptRewind.collectedBudget WalkLiteralLoop.budget
  change _≤(n+1)*(2^109*B)
  norm_num at hv repeated ⊢
  nlinarith only [hv,repeated,hback,hb]

end Theorem25Completion.CycleBounds
