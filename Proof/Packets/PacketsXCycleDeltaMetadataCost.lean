import Proof.Packets.PacketsXDeltaMetadata

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.CycleDeltaMetadataCost
open PCJ9eff70d512234a4c_Fixed.Materializer

theorem budget_formula (u n W parent child : Nat) :
    DeltaMetadata.budget u n W parent child=
      (n+parent+child+2*W)*(4*u+5)+2*n+88*u+162 := by
  have hs : min n W+(n-W)=n:=by omega
  have he:=congrArg (fun x=>x*(4*u+5)) hs
  simp only [DeltaMetadata.budget,DeltaScalarFields.budget,DeltaScalarFields.seedBudget,
    DeltaScalarFields.convertBudget,ScalarCounterSeed.budget,ScalarFromCounter.budget,
    ScalarTwice.budget,DeltaTargetGuard.budget]
  nlinarith only [he]

theorem budget_polynomial (C n W parent child : Nat) (hn : n≤C)
    (hp : parent≤C) (hc : child≤C) (hW : W≤64*(C+2)) :
    DeltaMetadata.budget (C+9) n W parent child+1≤32768*(C+1)^2 := by
  rw [budget_formula]
  have h:=Nat.mul_le_mul_right (4*(C+9)+5)
    (by omega : n+parent+child+2*W≤131*C+256)
  nlinarith only [h,hn,Nat.zero_le C,Nat.zero_le (C^2)]

theorem budget_reserve (C w n W parent child : Nat) (hn : n≤C)
    (hp : parent≤C) (hc : child≤C) (hW : W≤64*(C+2)) :
    DeltaMetadata.budget (C+9) n W parent child+1≤(65536*(C+1)^4*2^(8*w)) := by
  have hb:=budget_polynomial C n W parent child hn hp hc hW
  have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
  have hp : (C+1)^2≤(C+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith only [hb,Nat.mul_le_mul hp he,Nat.zero_le ((C+1)^2)]

theorem phase_width_reserve (C w population : Nat) (hp : population≤C) :
    128*(2*population+1)^2≤(65536*(C+1)^4*2^(8*w)) := by
  have hb:=Nat.pow_le_pow_left (by omega : 2*population+1≤2*(C+1)) 2
  have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
  have hpow : (C+1)^2≤(C+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith only [hb,Nat.mul_le_mul hpow he,Nat.zero_le ((C+1)^2)]

end Theorem25Completion.CycleDeltaMetadataCost
