import Proof.SourceAssembly.SourceSkelXtraF
import Proof.SourceAssembly.SourceStepsCallFacts
import Proof.SourceAssembly.SourceStepsF6
import Proof.SourceAssembly.SourceStepsNums

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
open NearCubicWires.SourceSteps
namespace NearCubicWires.SourceStart.SeamRP
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-! ## The onset -/

section onset
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

def seamOn (k den : ℕ) (hden : 1 ≤ den) : ℕ :=
  max (Classical.choose (ClassV4.seam_scalars_Rc4 selector mask packets rows sources gamma hg hh p k))
    (max (Classical.choose (ClassV4.seam_call_Rc4 selector mask packets rows sources gamma hg hh p k den hden))
      (max (Classical.choose (SourceBudget.widthAt_ge_eventually sources k
          (Classical.choose (SourceSteps.enc_sat_at sources k (SourceSteps.rBsel sources p)
            (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)))))
        (SourceSteps.selR sources p k).onset))

/-- **The seam rows' onset at the site** (index `kW`, denominator the fill's cap index `+ 1`), an `XtraW`-shaped onset to fold into `xtra`. -/
def seamOnW : ℕ :=
  seamOn selector mask packets rows sources gamma hg hh p (ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    ((ParamsV4.fPW selector (XtraF.xtraF selector) mask packets rows).capIndex sources gamma hg hh p + 1) (Nat.succ_pos _)

/-- Past `seamOnW`, `seamNumsRP`'s `hn` holds at the fill's index and denominator, at ANY onset `xtra` (both are `xtra`-free). -/
theorem seamOn_site (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (n : ℕ)
    (h : seamOnW selector mask packets rows sources gamma hg hh p ≤ n) :
    seamOn selector mask packets rows sources gamma hg hh p (FirstW.kSite selector xtra mask packets rows sources gamma hg hh p)
      ((ParamsV4.fPW selector xtra mask packets rows).capIndex sources gamma hg hh p + 1) (Nat.succ_pos _) ≤ n := h

end onset

/-! ## The entry-count helpers (at `N = |phaseE … ci|`) -/

section helpers
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den k : ℕ)

/-- The clause's entry count is its monomial count (`TraceData.hlen`; `order = monomials`). -/
theorem phaseE_len_monomials {n : ℕ} (x : BitInput n) (bits : List Bool) (mode : Bool) (ph : Phase) (L : ℕ)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) :
    (SourceSkeleton.phaseE sources p den k x bits mode ph L ci).length =
      (monomials (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length := by
  show (TraceData.entriesOf _ ph ci sources L _ mode).length = _
  rw [TraceData.hlen]
  rfl

theorem phaseE_len_le_b (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ} (hn : S.onset ≤ n)
    (x : BitInput n) (bits : List Bool) (mode : Bool) (ph : Phase) (L : ℕ)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) :
    (SourceSkeleton.phaseE sources p den k x bits mode ph L ci).length ≤ C10PartsSchedule.entryWidthSchedule sources k S.exponent n := by
  have h := SourceBudget.entry_count_le sources p den k S hn x bits mode ph L ci
    (SourceSkeleton.phaseE sources p den k x bits mode ph L ci).length
  simp only [List.length_append, List.length_take, min_self] at h
  omega

end helpers

section nums
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources res hres p k r ph' (refill3 mask packets rows sources res p k r se sp e (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "layA" => layoutAtOf sources selector coordC ph ci L tgtC modeC lay
set_option hygiene false in
local notation "factsA" => factsAtOf sources selector compiler coordC ph ci L tgtC modeC
set_option hygiene false in
local notation "vWS" => P1TopDownPaidReusableReserves.workspace (printerOf sources) V
set_option hygiene false in
local notation "vRW" => P1TopDownPaidReusableReserves.rewind (printerOf sources) V
set_option hygiene false in
local notation "vBF" => P1TopDownPaidReusableReserves.buffer V
set_option hygiene false in
local notation "vMB" => InitRun.Mb L vQ
set_option hygiene false in
local notation "vMS" => InitPost.Ms L vQ
set_option hygiene false in
local notation "vU0" => InitRun.U0 L vQ
set_option hygiene false in
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw (oldAt coordC ph ci sources L tgtC modeC b Dw) Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "vdX" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve

structure SeamNumsRP (ph : Phase)
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s) (g7cost : Nat → Nat)
    (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat) (Rc Rk b : Nat)
    (lay : TraceData.LayoutFamily coordC ph ci sources L tgtC modeC selector)
    (capsAt : Nat → RowCaps)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordC ph ci L tgtC modeC m) (layA m) (factsA m) (capsAt m))    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (old : Nat → List Bool)
    (familyCost firstCost counterReserve : Nat)
    (cW cQ cB cS refillCost N : Nat) : Prop where
  hRk : Rc ≤ Rk
  hcW : Rc ≤ cW
  hcQ : Rc ≤ cQ
  hcB : Rc ≤ cB
  hcS : Rc ≤ cS
  hSl : vWS + 2 ≤ Rc
  hRl : vRW + 2 ≤ Rc
  hBl : vBF + 2 ≤ Rc
  h4b : 4*b+5 ≤ Rc
  hUl : vU0 ≤ Rc
  hMb : vMB ≤ Rc
  hMs : vMS ≤ Rc
  hj : ∀ j, j < N → j + 1 ≤ (monomials coordC ph ci).length
  hRc : ∀ j, j < N → j + 1 + 3 ≤ Rc
  hlog : ∀ j, j < N → 2 * ((requestAt coordC ph ci L tgtC modeC (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc
  he1 : ∀ j, j < N → 1 ≤ PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))
  hpw : ∀ j, j < N → (CloseoutRowsCountBinary.bits (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)))).length ≤ b
  hfirst : ∀ j, j < N → PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * 2^(natBitLength (PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)))) < 2^b
  hsecond : ∀ j, j < N → PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * 2^(vQ+1) < 2^b
  hdescR : ∀ j, j < N → (capsAt (j+1)).descriptorReserve ≤ Rc
  hL : ∀ j, j < N → (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length + 3 ≤ Rc

set_option hygiene false in
local notation "𝔏𝔖" => ClassV4.siteL4 selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "ℜ𝔖" => (ClassV4.siteR4 selector mask packets rows).C sources gamma hg hh p *
  RuntimeShape.tableClass (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)
    ((ClassV4.siteR4 selector mask packets rows).hR sources gamma hg hh p) (C10PartsSchedule.widthAt sources k n)

theorem seamNumsRP (hg : 0 < gamma) (hh : gamma < 1/2) (ph : Phase)
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s) (g7cost : Nat → Nat)
    (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat) (Rc Rk b : Nat)
    (lay : TraceData.LayoutFamily coordC ph ci sources L tgtC modeC selector)
    (capsAt : Nat → RowCaps)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordC ph ci L tgtC modeC m) (layA m) (factsA m) (capsAt m))    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (old : Nat → List Bool)
    (familyCost firstCost counterReserve : Nat)
    (cW cQ cB cS refillCost N : Nat)
    (hn : seamOn selector mask packets rows sources gamma hg hh p k den hden ≤ n)
    (hr : r = SourceSteps.rBsel sources p)
    (hLe : L = 𝔏𝔖) (hRce : Rc = ℜ𝔖) (hbe : b = C10PartsSchedule.entryWidthSchedule sources k r n)
    (hVe : V = SourceBudget.Params.VvOf selector sources p 𝔏𝔖 (C10PartsSchedule.widthAt sources k n))
    (hcWe : cW = Rc) (hcQe : cQ = Rc) (hcBe : cB = Rc) (hcSe : cS = Rc)
    (hRk : Rc ≤ Rk) (hN : N ≤ (monomials coordC ph ci).length) (hNb : N ≤ b)
    (hcaps : ∀ m, (capsAt m).descriptorReserve ≤ V) :
    SeamNumsRP mask packets rows sources res p k r ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay
      capsAt goodAt K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N := by
  subst hcWe hcQe hcBe hcSe
  unfold seamOn at hn
  simp only [max_le_iff] at hn
  obtain ⟨n1, n2, n3, n4⟩ := hn
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    Classical.choose_spec (ClassV4.seam_scalars_Rc4 selector mask packets rows sources gamma hg hh p k) n n1
  have hcall := Classical.choose_spec (ClassV4.seam_call_Rc4 selector mask packets rows sources gamma hg hh p k den hden) n n2
  have hq0 := Classical.choose_spec (SourceBudget.widthAt_ge_eventually sources k
    (Classical.choose (SourceSteps.enc_sat_at sources k (SourceSteps.rBsel sources p) 𝔏𝔖))) n n3
  have henc := Classical.choose_spec (SourceSteps.enc_sat_at sources k (SourceSteps.rBsel sources p) 𝔏𝔖) n hq0
    ((ClassV4.siteR4 selector mask packets rows).C sources gamma hg hh p) ((ClassV4.siteR4 selector mask packets rows).hR sources gamma hg hh p) le_rfl
  have hcut := SourceSteps.selR_cutoff sources p k n4
  have hq : (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity =
      C10PartsSchedule.widthAt sources k n :=
    Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x _ hcut
  have hfacts := fun m => SourceSteps.site_call_facts sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ph ci L hden hcut m
  subst hr hLe hRce hbe hVe
  refine
    { hRk := hRk, hcW := le_rfl, hcQ := le_rfl, hcB := le_rfl, hcS := le_rfl, hSl := a1, hRl := a2, hBl := a3, h4b := henc,
      hUl := ?_, hMb := ?_, hMs := ?_, hj := fun j hj => by omega, hRc := fun j hj => by omega,
      hlog := fun j _ => (hcall _ (hfacts (j+1)).1 (hfacts (j+1)).2.2 (hfacts (j+1)).2.1).1,
      he1 := fun j _ => SourceSteps.seedCount_pos _ _,
      hpw := fun j _ => SourceSteps.f6_hpw sources p den hden k _ (scratchOf mask packets rows sources res) n x bits hp ph ci _ (SourceSteps.selR sources p k) n4 rfl (j+1),
      hfirst := fun j _ => SourceSteps.f6_hfirst sources p den hden k _ (scratchOf mask packets rows sources res) n x bits hp ph ci _ (SourceSteps.selR sources p k) n4 rfl (j+1),
      hsecond := fun j _ => SourceSteps.f6_hsecond sources p den hden k _ (scratchOf mask packets rows sources res) n x bits hp ph ci _ (SourceSteps.selR sources p k) n4 rfl (j+1),
      hdescR := fun j _ => (hcaps (j+1)).trans a4,
      hL := fun j _ => (hcall _ (hfacts (j+1)).1 (hfacts (j+1)).2.2 (hfacts (j+1)).2.1).2 }
  · rw [hq]; exact a5
  · rw [hq]; exact a6
  · rw [hq]; exact a7

end nums

end
end NearCubicWires.SourceStart.SeamRP
end

