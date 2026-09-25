import Proof.Packets.PacketsXWindowLiteralProvider
import Proof.Packets.CycleWindowSeedCost

/-! The two nested literal-window loops cost only a polynomial multiple of
the common reserve. This does not add another exponential power of the degree
policy when the literal provider is used inside the vector controller. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open Theorem25Completion

theorem emitted_loop_budget (u d R : Nat) (hR : 1≤ R) (hu : u≤ R) (hd : d≤ R) :
    DescendingWindowLoop.budget u d R≤148*(d+1)^2*R := by
  have hp : R≤(d+1)*R:=by nlinarith
  have iter : DescendingWindow.iterationBudget u d R+3≤96*R := by
    unfold DescendingWindow.iterationBudget
    omega
  have inner : DescendingWindow.budget u d R≤99*(d+1)*R := by
    have h:=Nat.mul_le_mul_left (d+1) iter
    unfold DescendingWindow.budget
    nlinarith only [h,hp,hR]
  have outer : DescendingWindowOuter.budget u d R+3≤145*(d+1)*R := by
    unfold DescendingWindowOuter.budget
    nlinarith only [inner,hu,hd,hR,hp]
  have h:=Nat.mul_le_mul_left (d+1) outer
  have hpp : R≤(d+1)^2*R:=by nlinarith
  unfold DescendingWindowLoop.budget
  nlinarith only [h,hpp,hR]

theorem literal_provider_budget (C w v M W offset target : Nat) (codes : List Nat)
    (hc : codes.Pairwise (·<·)) (hcodes : ∀c∈codes,c< C) (hlen : codes.length=M)
    (hM : M≤ C) (hv : v≤ C+1) (hMv : M≤2^v) (hw : 3≤ w)
    (hW : W≤64*(C+2)) (hd : 2*W+1≤2^w) (hcount : (M+1)^(2*W)≤2^w) :
    literalProviderBudget C (CycleBounds.commonReserve C w) v (C+9) M offset W target codes≤
      2199023255552*(C+1)^6*2^(8*w) := by
  let R:=CycleBounds.commonReserve C w
  have raw:=literal_consume_budget C w codes hc hcodes (by omega) v offset (2*W) target
    (by omega) hw hd (by simpa only [hlen] using hcount)
  have seed:=CycleWindowSeedCost.budget_reserve C w v M W (by omega) hv hM hW
  have reserveEq : CycleCommonReserve.reserve C w=R:=rfl
  change WindowSeed.budget (CycleCommonReserve.reserve C w) v (C+9) M W≤17*CycleCommonReserve.reserve C w at seed
  rw [reserveEq] at seed
  have large : 65536*(C+1)≤ R := by
    have hp : C+1≤(C+1)^4:=Nat.le_self_pow (by decide) _
    have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
    have h:=Nat.mul_le_mul hp he
    dsimp [R,CycleBounds.commonReserve]
    nlinarith only [h]
  have dsmall : 2*W+1≤257*(C+1):=by omega
  have loop:=emitted_loop_budget (C+9) (2*W) R (by omega) (by omega) (by omega)
  have hbase : R≤(2*W+1)^2*R:=by
    have hp : 1≤(2*W+1)^2:=Nat.one_le_pow _ _ (by omega)
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right R hp
  have total : literalProviderBudget C R v (C+9) M offset W target codes≤256*(2*W+1)^2*R := by
    unfold literalProviderBudget WindowSeed.completeBudget
    nlinarith only [seed,raw,loop,hbase,large,Nat.zero_le C]
  have hsquare:=Nat.pow_le_pow_left dsmall 2
  have mult:=Nat.mul_le_mul_right R hsquare
  have bound : literalProviderBudget C R v (C+9) M offset W target codes≤33554432*(C+1)^2*R := by
    nlinarith only [total,mult,Nat.zero_le ((C+1)^2*R)]
  calc
    literalProviderBudget C (CycleBounds.commonReserve C w) v (C+9) M offset W target codes
        ≤33554432*(C+1)^2*R:=bound
    _=2199023255552*(C+1)^6*2^(8*w):=by dsimp [R,CycleBounds.commonReserve];ring

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
