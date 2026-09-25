import Proof.Packets.BudgetCallRest
import Proof.Packets.BudgetPoly
import Proof.Packets.BudgetSiteInit

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- Transport along the live scale (avoids `rw` motives through the class witnesses). -/
theorem InClasses.congr_L {dP hT hS m L L' n qn cP cT cS x : ℕ} (h : L = L')
    (hx : InClasses dP hT hS m L n qn cP cT cS x) : InClasses dP hT hS m L' n qn cP cT cS x := h ▸ hx

/-! ## Closed data: P's cold cache constants, PM/PG's stages -/

/-- P's cold-cache coefficient (`Cold.coldBudget_poly`, POOL-8). -/
def coldC : ℕ := Classical.choose Cold.coldBudget_poly
/-- P's cold-cache exponent. -/
def coldD : ℕ := Classical.choose (Classical.choose_spec Cold.coldBudget_poly)

theorem cold_spec : ∀ (q : ℕ) (x : BinaryCacheColdJoin.Args q), BinaryCacheColdRun.budget x ≤
    coldC * ((exactListWord x.gs).length + x.gs.length + q + 2^x.live.card + 1)^coldD :=
  Classical.choose_spec (Classical.choose_spec Cold.coldBudget_poly)

abbrev seOf (sources : EightSources) : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources)
    (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) :=
  PacketsMeta.Seed.seedCountStage (decompositionOf sources)

abbrev spOf (sources : EightSources) : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources)
    (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) :=
  PacketsGlue.RequestMeta.primeCountStage (decompositionOf sources) (PacketsMeta.cutoffStage (decompositionOf sources))

/-- A per-parameter size-constant family; the last argument is the live scale `L` (AD's header class reads it). -/
abbrev CallKFam : Type :=
  (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → CallK

section fam
variable {selector : CyclicChoice.Laws} (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (degreeOf targetOf : ParNat) (KF : CallKFam)

/-- The small-size degree covering every small summand of the call. -/
def DmOf (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  (packets (decompositionOf sources)).degree + (rows (decompositionOf sources) (printerOf sources)).degree +
    (betaE (decompositionOf sources) (degreeOf sources gamma hg hh p) + 1)*coldD + (seOf sources).degree +
    (spOf sources).degree + 2*(163+3) + 1

theorem DmOf_spec (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (packets (decompositionOf sources)).degree ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧
    (rows (decompositionOf sources) (printerOf sources)).degree ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧
    (betaE (decompositionOf sources) (degreeOf sources gamma hg hh p) + 1)*coldD ≤
      DmOf packets rows degreeOf sources gamma hg hh p ∧
    (seOf sources).degree ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧
    (spOf sources).degree ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧
    2*(163+3) ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧ 1 ≤ DmOf packets rows degreeOf sources gamma hg hh p := by
  unfold DmOf; omega

/-- **The refill class family `y`** (coefficients at the live scale `Lf`). -/
def yFam (Lf : ParNat) : ClsFam where
  dP := fun s g hg hh p => (KF s g hg hh p 0).D mask.degree
  hT := fun s g hg hh p => (KF s g hg hh p 0).H (rows (decompositionOf s) (printerOf s)).degree
  hS := fun s g hg hh p L => (KF s g hg hh p L).S
  cP := fun s g hg hh p k =>
    Classical.choose (ycall_cls mask (packets (decompositionOf s)) (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s)
      (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD cold_spec (KF s g hg hh p (Lf s g hg hh p))
      (DmOf packets rows degreeOf s g hg hh p) (DmOf_spec packets rows degreeOf s g hg hh p)) *
    C10PartsSchedule.widthConst s k ^ ((KF s g hg hh p 0).D mask.degree)
  cT := fun s g hg hh p _ =>
    Classical.choose (Classical.choose_spec (ycall_cls mask (packets (decompositionOf s)) (rows (decompositionOf s) (printerOf s))
      (seOf s) (spOf s) (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD cold_spec (KF s g hg hh p (Lf s g hg hh p))
      (DmOf packets rows degreeOf s g hg hh p) (DmOf_spec packets rows degreeOf s g hg hh p)))
  cS := fun s g hg hh p _ =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (ycall_cls mask (packets (decompositionOf s))
      (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s) (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD
      cold_spec (KF s g hg hh p (Lf s g hg hh p)) (DmOf packets rows degreeOf s g hg hh p)
      (DmOf_spec packets rows degreeOf s g hg hh p))))

/-- **The first cycle's `Rc`-free class family `yF0`** (coefficients at the live scale `Lf`). -/
def yF0Fam (Lf : ParNat) : ClsFam where
  dP := fun s g hg hh p => (KF s g hg hh p 0).D mask.degree
  hT := fun s g hg hh p => (KF s g hg hh p 0).H (rows (decompositionOf s) (printerOf s)).degree
  hS := fun s g hg hh p L => (KF s g hg hh p L).S
  cP := fun s g hg hh p k =>
    Classical.choose (yF0call_cls mask (packets (decompositionOf s)) (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s)
      (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD cold_spec (KF s g hg hh p (Lf s g hg hh p))
      (DmOf packets rows degreeOf s g hg hh p) (DmOf_spec packets rows degreeOf s g hg hh p)) *
    C10PartsSchedule.widthConst s k ^ ((KF s g hg hh p 0).D mask.degree)
  cT := fun s g hg hh p _ =>
    Classical.choose (Classical.choose_spec (yF0call_cls mask (packets (decompositionOf s))
      (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s) (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD
      cold_spec (KF s g hg hh p (Lf s g hg hh p)) (DmOf packets rows degreeOf s g hg hh p)
      (DmOf_spec packets rows degreeOf s g hg hh p)))
  cS := fun s g hg hh p _ =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (yF0call_cls mask (packets (decompositionOf s))
      (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s) (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD
      cold_spec (KF s g hg hh p (Lf s g hg hh p)) (DmOf packets rows degreeOf s g hg hh p)
      (DmOf_spec packets rows degreeOf s g hg hh p))))

/-- The exponents of `KF` do not read the live scale (true for AD's constants: only the header's SMALL exponent does). -/
def KFree (KF : CallKFam) (md rd : EightSources → ℕ) : Prop :=
  ∀ (s : EightSources) (g : Real) (hg : 0 < g) (hh : g < 1/2) (p : Parameters s g) (L : ℕ),
    (KF s g hg hh p L).D (md s) = (KF s g hg hh p 0).D (md s) ∧ (KF s g hg hh p L).H (rd s) = (KF s g hg hh p 0).H (rd s)

variable (Lf : ParNat)

/-- **`y` at a site call**: the refill's `Rc`-free quantity lies in `(yFam … Lf).at … (Lf …) k` at the input length `n`, from the call's
size facts at `KF … (Lf …)`, once the call's arity is `widthAt sources k n` and its live scale is `Lf …`. -/
theorem yFam_site (hKF : KFree KF (fun _ => mask.degree) (fun s => (rows (decompositionOf s) (printerOf s)).degree))
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (k n den : ℕ) (r : Request)
    (layout : Packets.Layout (decompositionOf sources) (r.family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) r))
    (facts : ∀ row ∈ (r.family (decompositionOf sources)).rows, Packets.PacketFacts (decompositionOf sources)
      (r.family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) r) row)
    (caps : RowCaps) (g7cost : ℕ → ℕ) (w Mb Ms U0 V v j : ℕ)
    (hq : r.q = C10PartsSchedule.widthAt sources k n) (hL : r.liveScale = Lf sources gamma hg hh p)
    (hden : 1 ≤ den) (hr : RequestAdmitted den (degreeOf sources gamma hg hh p) (targetOf sources gamma hg hh p) r)
    (hin : (r.input (decompositionOf sources)).length ≤
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).inC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).inE)
    (hrows : (r.family (decompositionOf sources)).rows.length + 1 ≤
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).rowsC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).rowsE)
    (hsm : (r.smallSize (decompositionOf sources))^(DmOf packets rows degreeOf sources gamma hg hh p) ≤ 1*smallClass 4 0 r.q)
    (hlw : layout.w ≤ r.q) (hld : layout.degree ≤ r.q)
    (hlC : layout.C ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).capC*
      smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).capE r.q)
    (hhd : caps.headerFuel ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).hdC*
      smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).hdE r.q)
    (hcp : caps.copyCap ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cpTC*
        tableClass r.liveScale (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cpTE r.q +
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cpSC*
        smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cpSE r.q)
    (hds : caps.descriptorReserve ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).dsTC*
        tableClass r.liveScale (KF sources gamma hg hh p (Lf sources gamma hg hh p)).dsTE r.q +
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).dsSC*
        smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).dsSE r.q)
    (hraw : caps.rawReserve ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).rwC*
      smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).rowsE r.q)
    (hgood : RowCaps.Good selector (decompositionOf sources) (printerOf sources) r layout facts caps)
    (hgs : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
        (r.family (decompositionOf sources))).gs).length + 1 ≤
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).betC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).betE)
    (hMb : Mb ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).mC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).mE)
    (hMs : Ms ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).mC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).mE)
    (hU0 : U0 ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).mC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).mE)
    (hw : w ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).bC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).bE)
    (hv : v ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).bC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).bE)
    (hj : j ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).jC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).jE)
    (hV : V ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cVc*
      tableClass r.liveScale (KF sources gamma hg hh p (Lf sources gamma hg hh p)).hV r.q)
    (hg7 : g7cost (j+1) ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cG*
      (r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).dG) :
    ((yFam mask packets rows degreeOf targetOf KF Lf).at sources gamma hg hh p (Lf sources gamma hg hh p) k).In 4
      (Lf sources gamma hg hh p) n (C10PartsSchedule.widthAt sources k n)
      (Rest.restCost (seOf sources) (spOf sources) g7cost r 0 w r.q
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r.family (decompositionOf sources))).gs).length
          Mb Ms j +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) r layout facts caps
          (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
            (r.family (decompositionOf sources))).gs).length then Mb else Ms) U0
          (P1TopDownPaidReusableReserves.workspace (printerOf sources) V)
          (P1TopDownPaidReusableReserves.rewind (printerOf sources) V) (P1TopDownPaidReusableReserves.buffer V) v 0) := by
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (ycall_cls mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources)) (seOf sources) (spOf sources) (degreeOf sources gamma hg hh p)
      (targetOf sources gamma hg hh p) coldC coldD cold_spec (KF sources gamma hg hh p (Lf sources gamma hg hh p))
      (DmOf packets rows degreeOf sources gamma hg hh p) (DmOf_spec packets rows degreeOf sources gamma hg hh p))))
  have h := hspec den r layout facts caps g7cost w Mb Ms U0 V v j hden hr hin hrows hsm hlw hld hlC hhd hcp hds hraw hgood hgs
    hMb hMs hU0 hw hv hj hV hg7
  have h1 := InClasses.raise (le_of_eq (hKF sources gamma hg hh p (Lf sources gamma hg hh p)).1)
    (le_of_eq (hKF sources gamma hg hh p (Lf sources gamma hg hh p)).2) le_rfl h
  have h2 := InClasses.congr_L hL h1
  have hW : r.q + 1 ≤ C10PartsSchedule.widthConst sources k * (n+1) := by
    have hw := SourcePhase.widthAt_poly sources k n
    rw [pow_one] at hw; rw [hq]; exact hw
  rw [← hq]
  exact InClasses.lift_n hW h2

/-- **`yF0` at a site call** (the first cycle's `Rc`-free rest), as `yFam_site`. -/
theorem yF0Fam_site (hKF : KFree KF (fun _ => mask.degree) (fun s => (rows (decompositionOf s) (printerOf s)).degree))
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (k n den : ℕ) (r : Request)
    (layout : Packets.Layout (decompositionOf sources) (r.family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) r))
    (facts : ∀ row ∈ (r.family (decompositionOf sources)).rows, Packets.PacketFacts (decompositionOf sources)
      (r.family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) r) row)
    (caps : RowCaps) (g7cost : ℕ → ℕ) (w Mb Ms U0 V v C : ℕ)
    (hq : r.q = C10PartsSchedule.widthAt sources k n) (hL : r.liveScale = Lf sources gamma hg hh p)
    (hden : 1 ≤ den) (hr : RequestAdmitted den (degreeOf sources gamma hg hh p) (targetOf sources gamma hg hh p) r)
    (hin : (r.input (decompositionOf sources)).length ≤
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).inC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).inE)
    (hrows : (r.family (decompositionOf sources)).rows.length + 1 ≤
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).rowsC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).rowsE)
    (hsm : (r.smallSize (decompositionOf sources))^(DmOf packets rows degreeOf sources gamma hg hh p) ≤ 1*smallClass 4 0 r.q)
    (hlw : layout.w ≤ r.q) (hld : layout.degree ≤ r.q)
    (hlC : layout.C ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).capC*
      smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).capE r.q)
    (hhd : caps.headerFuel ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).hdC*
      smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).hdE r.q)
    (hcp : caps.copyCap ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cpTC*
        tableClass r.liveScale (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cpTE r.q +
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cpSC*
        smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cpSE r.q)
    (hds : caps.descriptorReserve ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).dsTC*
        tableClass r.liveScale (KF sources gamma hg hh p (Lf sources gamma hg hh p)).dsTE r.q +
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).dsSC*
        smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).dsSE r.q)
    (hraw : caps.rawReserve ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).rwC*
      smallClass 4 (KF sources gamma hg hh p (Lf sources gamma hg hh p)).rowsE r.q)
    (hgood : RowCaps.Good selector (decompositionOf sources) (printerOf sources) r layout facts caps)
    (hgs : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
        (r.family (decompositionOf sources))).gs).length + 1 ≤
      (KF sources gamma hg hh p (Lf sources gamma hg hh p)).betC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).betE)
    (hMb : Mb ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).mC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).mE)
    (hMs : Ms ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).mC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).mE)
    (hU0 : U0 ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).mC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).mE)
    (hw : w ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).bC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).bE)
    (hv : v ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).bC*(r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).bE)
    (hV : V ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cVc*
      tableClass r.liveScale (KF sources gamma hg hh p (Lf sources gamma hg hh p)).hV r.q)
    (hg7 : g7cost 0 ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cG*
      (r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).dG)
    (hC : C ≤ (KF sources gamma hg hh p (Lf sources gamma hg hh p)).cwC*
      (r.q+1)^(KF sources gamma hg hh p (Lf sources gamma hg hh p)).cwE) :
    ((yF0Fam mask packets rows degreeOf targetOf KF Lf).at sources gamma hg hh p (Lf sources gamma hg hh p) k).In 4
      (Lf sources gamma hg hh p) n (C10PartsSchedule.widthAt sources k n)
      (6*C + g7cost 0 + Rest.backCost (seOf sources) (spOf sources) r 0 w r.q
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r.family (decompositionOf sources))).gs).length
          Mb Ms +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) r layout facts caps
          (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
            (r.family (decompositionOf sources))).gs).length then Mb else Ms) U0
          (P1TopDownPaidReusableReserves.workspace (printerOf sources) V)
          (P1TopDownPaidReusableReserves.rewind (printerOf sources) V) (P1TopDownPaidReusableReserves.buffer V) v 0) := by
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (yF0call_cls mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources)) (seOf sources) (spOf sources) (degreeOf sources gamma hg hh p)
      (targetOf sources gamma hg hh p) coldC coldD cold_spec (KF sources gamma hg hh p (Lf sources gamma hg hh p))
      (DmOf packets rows degreeOf sources gamma hg hh p) (DmOf_spec packets rows degreeOf sources gamma hg hh p))))
  have h := hspec den r layout facts caps g7cost w Mb Ms U0 V v C hden hr hin hrows hsm hlw hld hlC hhd hcp hds hraw hgood hgs
    hMb hMs hU0 hw hv hV hg7 hC
  have h1 := InClasses.raise (le_of_eq (hKF sources gamma hg hh p (Lf sources gamma hg hh p)).1)
    (le_of_eq (hKF sources gamma hg hh p (Lf sources gamma hg hh p)).2) le_rfl h
  have h2 := InClasses.congr_L hL h1
  have hW : r.q + 1 ≤ C10PartsSchedule.widthConst sources k * (n+1) := by
    have hw := SourcePhase.widthAt_poly sources k n
    rw [pow_one] at hw; rw [hq]; exact hw
  rw [← hq]
  exact InClasses.lift_n hW h2

end fam

end
end NearCubicWires.SourceBudget
end

