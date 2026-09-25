import Proof.SourceAssembly.AdmissionPhase
import Proof.SourceAssembly.SourcePhaseFuel

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.Admission
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule

noncomputable section

structure J5Consts where
  dS : ℕ
  hT : ℕ
  hS : ℕ
  m : ℕ
  L : ℕ
  cP : ℕ
  cT : ℕ
  cS : ℕ
  nC : ℕ
  nE : ℕ
  sC : ℕ
  sE : ℕ
  xC : ℕ
  xE : ℕ
  eC : ℕ
  eE : ℕ
  wC : ℕ
  wE : ℕ

namespace J5Consts
variable (K : J5Consts) (a : RepairRepresentation.PointwisePCPPAlgorithm)

/-- One common source degree dominating every component's. -/
def D : ℕ := K.dS + K.nE + K.sE*PCPPQueryCachedBounds.degree a + 5*K.xE + 2*K.wE + K.eE

/-- The recipe's `remainingDegree`. -/
def degree : ℕ := K.nE + K.D a

/-- The table exponent (the `Split.order` constraint is `tableExp + σ + 2 ≤ L`). -/
def tableExp : ℕ := K.nE + K.hT

def smallExp : ℕ := K.nE + K.hS

/-- One phase's common source-polynomial coefficient (site + PCPP query term + fold + entry). -/
def base : ℕ :=
  K.cP + (4*PCPPQueryCachedBounds.coefficient a*K.sC^PCPPQueryCachedBounds.degree a + 7) +
    3800000*K.xC^5 + K.eC

def phaseP : ℕ := K.base a + K.nC*(K.base a + K.base a + 4*K.nC + 24) + K.base a + 5
def phaseT : ℕ := K.cT + K.nC*(K.cT + K.cT) + K.cT
def phaseS : ℕ := K.cS + K.nC*(K.cS + K.cS) + K.cS

def coefP : ℕ := 3*K.phaseP a + (1000000*K.wC^2 + 5)
def coefT : ℕ := 3*K.phaseT
def coefS : ℕ := 3*K.phaseS

/-- **The J5 right-hand side**: `remainingFuel n := K.fuel a n (q n)`. -/
def fuel (n qn : ℕ) : ℕ :=
  splitRHS (K.degree a) K.tableExp K.smallExp K.m K.L (K.coefP a) K.coefT K.coefS n qn

end J5Consts

/-- **One phase in the classes.** The phase fuel of `MaskedPhase` / `ofLoops` (`hfp`) at the minimal
`c := 4N + callBudget s + siteFuel + 21`, from the site class, the clause count, the request size, the fold
arguments and the entry bound. -/
theorem phase_inClasses (K : J5Consts) (a : RepairRepresentation.PointwisePCPPAlgorithm) {n qn : ℕ}
    {N s siteFuel entryFuel b count : ℕ}
    (hNn : N ≤ K.nC*(n+1)^K.nE) (hNq : N ≤ K.nC*(qn+1)^K.nE)
    (hs : s + 1 ≤ K.sC*(n+1)^K.sE)
    (hx : b + count + 1 ≤ K.xC*(n+1)^K.xE)
    (he : entryFuel ≤ K.eC*(n+1)^K.eE)
    (hsite : InClasses K.dS K.hT K.hS K.m K.L n qn K.cP K.cT K.cS siteFuel) :
    InClasses (K.degree a) K.tableExp K.smallExp K.m K.L n qn (K.phaseP a) K.phaseT K.phaseS
      (entryFuel+1+(N*((4*N+PCPPQueryCachedBounds.callBudget a s+siteFuel+21)+3)+3+1+
        CloseoutFinalC10RetainedPhaseFold.fuel b count)) := by
  have hsD : K.sE*PCPPQueryCachedBounds.degree a ≤ K.D a := by unfold J5Consts.D; omega
  have hxD : 5*K.xE ≤ K.D a := by unfold J5Consts.D; omega
  have heD : K.eE ≤ K.D a := by unfold J5Consts.D; omega
  have hnD : K.nE ≤ K.D a := by unfold J5Consts.D; omega
  have hdD : K.dS ≤ K.D a := by unfold J5Consts.D; omega
  have hCall := callBudget_inClasses (dP := K.D a) (hT := K.hT) (hS := K.hS) (m := K.m) (L := K.L)
    (n := n) (qn := qn) a s K.sC K.sE hs hsD
  have hFold := SourcePhase.foldFuel_inClasses (dP := K.D a) (hT := K.hT) (hS := K.hS) (m := K.m)
    (L := K.L) (n := n) (qn := qn) b count K.xC K.xE hx hxD
  have hEntry : InClasses (K.D a) K.hT K.hS K.m K.L n qn K.eC 0 0 entryFuel := InClasses.poly he heD
  have hSite := hsite.raise (dP' := K.D a) (hT' := K.hT) (hS' := K.hS) hdD le_rfl le_rfl
  have hb1 : K.eC ≤ K.base a := by unfold J5Consts.base; omega
  have hb2 : 4*PCPPQueryCachedBounds.coefficient a*K.sC^PCPPQueryCachedBounds.degree a + 7 ≤ K.base a := by
    unfold J5Consts.base; omega
  have hb3 : 3800000*K.xC^5 ≤ K.base a := by unfold J5Consts.base; omega
  have hb4 : K.cP ≤ K.base a := by unfold J5Consts.base; omega
  have h := phaseFuel_inClasses hNn hNq hnD
    (hEntry.coeff_mono (cP' := K.base a) (cT' := K.cT) (cS' := K.cS) hb1 (Nat.zero_le _) (Nat.zero_le _))
    (hCall.coeff_mono (cP' := K.base a) (cT' := K.cT) (cS' := K.cS) hb2 (Nat.zero_le _) (Nat.zero_le _))
    (hSite.coeff_mono (cP' := K.base a) (cT' := K.cT) (cS' := K.cS) hb4 le_rfl le_rfl)
    (hFold.coeff_mono (cP' := K.base a) (cT' := K.cT) (cS' := K.cS) hb3 (Nat.zero_le _) (Nat.zero_le _))
  exact h

/-- **J5, generic in the phase data.** Three phases whose fuels have `ofLoops`' form (`hcost`), each at a
`c` no larger than the minimal one (`hcp`: the witness chooses `c` equal to it), and fold widths polynomial
in `n`, give the consumer's `branchFuel cost width + 2 ≤ remainingFuel` at `remainingFuel := K.fuel a n qn`. -/
theorem fits_generic (K : J5Consts) (a : RepairRepresentation.PointwisePCPPAlgorithm) {n qn : ℕ}
    (cost width : Phase → ℕ) (N s b : ℕ) (entryFuel siteFuel count c : Phase → ℕ)
    (hNn : N ≤ K.nC*(n+1)^K.nE) (hNq : N ≤ K.nC*(qn+1)^K.nE)
    (hs : s + 1 ≤ K.sC*(n+1)^K.sE)
    (hx : ∀ ph, b + count ph + 1 ≤ K.xC*(n+1)^K.xE)
    (he : ∀ ph, entryFuel ph ≤ K.eC*(n+1)^K.eE)
    (hsite : ∀ ph, InClasses K.dS K.hT K.hS K.m K.L n qn K.cP K.cT K.cS (siteFuel ph))
    (hc : ∀ ph, c ph ≤ 4*N + PCPPQueryCachedBounds.callBudget a s + siteFuel ph + 21)
    (hcost : ∀ ph, cost ph = entryFuel ph + 1 + (N*(c ph+3)+3+1+
      CloseoutFinalC10RetainedPhaseFold.fuel b (count ph)))
    (hW : ∀ ph, width ph + 1 ≤ K.wC*(n+1)^K.wE) :
    PCJ374c44bb8b7f47d9_.branchFuel cost width + 2 ≤ K.fuel a n qn := by
  have hph : ∀ ph, InClasses (K.degree a) K.tableExp K.smallExp K.m K.L n qn (K.phaseP a) K.phaseT
      K.phaseS (cost ph) := by
    intro ph
    refine InClasses.mono ?_ (phase_inClasses K a hNn hNq hs (hx ph) (he ph) (hsite ph))
    rw [hcost ph]
    have := Nat.mul_le_mul_left N (Nat.add_le_add_right (hc ph) 3)
    omega
  have hwd : 2*K.wE ≤ K.degree a := by unfold J5Consts.degree J5Consts.D; omega
  have h := branchFuel_of_phases cost width (K.degree a) K.tableExp K.smallExp K.m K.L n qn
    (K.phaseP a) K.phaseT K.phaseS K.wC K.wE hph (SourcePhase.widths_hW width n K.wC K.wE hW) hwd
  exact h

end
end NearCubicWires.SourceBudget

