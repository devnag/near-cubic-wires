import Proof.Packets.SrcSeamFamH
import Proof.Packets.SrcLayRows
import Proof.SourceAssembly.SourceFactorSelClauseCost

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
open NearCubicWires.SourceBudget NearCubicWires.SourceStart.SeamRP
namespace NearCubicWires.SourceFactorSel.SeamSiteGF
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

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

set_option hygiene false in
local notation "𝔏𝔖" => ClassV4.siteL4 selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "ℜ𝔖" => (ClassV4.siteR4 selector mask packets rows).C sources gamma hg hh p *
  RuntimeShape.tableClass (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)
    ((ClassV4.siteR4 selector mask packets rows).hR sources gamma hg hh p) (C10PartsSchedule.widthAt sources k n)

def siteOnGF (hg : 0 < gamma) (hh : gamma < 1/2) (den : ℕ) (hden : 1 ≤ den) : ℕ :=
  max (seamOn selector mask packets rows sources gamma hg hh p (ParamsV4.kW selector mask packets rows sources gamma hg hh p) den hden)
    (max (hfamOnW selector mask packets rows sources gamma hg hh p)
      (max (NearCubicWires.SourceStart.LayRP.layOnW selector mask packets rows sources gamma hg hh p)
        (max (SourceSteps.selR sources p (ParamsV4.kW selector mask packets rows sources gamma hg hh p)).onset
          (NearCubicWires.SourceFactorSel.ClauseCost.refOnS selector mask packets rows sources gamma hg hh p
            (SourceBudget.capIndexOf (ParamsV4.den0W selector mask packets rows))))))

/-- `seamOn` at the site index (proof-irrelevant in the index equation). -/
theorem seamOn_of (hg : 0 < gamma) (hh : gamma < 1/2) (k' : ℕ) (hk : k' = ParamsV4.kW selector mask packets rows sources gamma hg hh p) (den n : ℕ)
    (hden : 1 ≤ den) (h : seamOn selector mask packets rows sources gamma hg hh p (ParamsV4.kW selector mask packets rows sources gamma hg hh p) den hden ≤ n) :
    seamOn selector mask packets rows sources gamma hg hh p k' den hden ≤ n := by
  subst hk; exact h

/-- `hfamOn` at the site index, for ANY clock proof. -/
theorem hfamOn_of (hg : 0 < gamma) (hh : gamma < 1/2) (k' : ℕ) (hk : k' = ParamsV4.kW selector mask packets rows sources gamma hg hh p) (n : ℕ)
    (hkc : (famW selector sources gamma hg hh p k').dP + 1 ≤ k' + 2) (h : hfamOnW selector mask packets rows sources gamma hg hh p ≤ n) :
    hfamOn selector sources gamma hg hh p k' 𝔏𝔖 hkc ≤ n := by
  subst hk; exact h

/-- The clock condition at the site index. -/
theorem clock_of (hg : 0 < gamma) (hh : gamma < 1/2) (k' : ℕ) (hk : k' = ParamsV4.kW selector mask packets rows sources gamma hg hh p) :
    (famW selector sources gamma hg hh p k').dP + 1 ≤ k' + 2 := by
  subst hk; exact famSite_dP_le_kW selector mask packets rows sources gamma hg hh p

theorem seamRP_site (hg : 0 < gamma) (hh : gamma < 1/2) (ph : Phase)
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
    (hk : k = ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    (hr : r = SourceSteps.rBsel sources p)
    (hLe : L = 𝔏𝔖) (hRce : Rc = ℜ𝔖) (hRke : Rk = 16 * (Rc + 1)) (hbe : b = C10PartsSchedule.entryWidthSchedule sources k r n)
    (hVe : V = SourceBudget.Params.VvOf selector sources p 𝔏𝔖 (C10PartsSchedule.widthAt sources k n))
    (hcWe : cW = Rc) (hcQe : cQ = Rc) (hcBe : cB = Rc) (hcSe : cS = Rc)
    (hcapsD : ∀ m, (capsAt m).descriptorReserve = V) (hDwe : Dw = NearCubicWires.SourceConstruction.InitRun.D0 b)
    (hrefill : refillCost = NearCubicWires.SourceFactorSel.ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hNe : N = (SourceSkeleton.phaseE sources p den k x bits modeC ph L ci).length)
    (hlayD : ∀ j, (lay j).degree = Admission.uniformDeg vQ L)
    (hon : siteOnGF mask packets rows sources p hg hh den hden ≤ n) :
    SeamNumsRP mask packets rows sources res p k r ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay capsAt goodAt K K0 KH0 V dflt Dw capw logw resetw
      Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N := by
  unfold siteOnGF at hon
  simp only [max_le_iff] at hon
  obtain ⟨o1, -, -, o4, -⟩ := hon
  have o4' : (SourceSteps.selR sources p k).onset ≤ n := by rw [hk]; exact o4
  have hN : N ≤ (monomials coordC ph ci).length := by
    rw [hNe, phaseE_len_monomials sources p den k x bits modeC ph L ci]
  have hNb : N ≤ b := by
    rw [hNe, hbe]
    exact (phaseE_len_le_b sources p den k (SourceSteps.selR sources p k) o4' x bits modeC ph L ci).trans
      (le_of_eq (congrArg (fun e => C10PartsSchedule.entryWidthSchedule sources k e n) hr.symm))
  exact seamNumsRP mask packets rows sources res p k r hg hh ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay
    capsAt goodAt K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N
    (seamOn_of mask packets rows sources p hg hh k hk den n hden o1) hr hLe hRce hbe hVe hcWe hcQe hcBe hcSe (by omega) hN hNb
    (fun m => le_of_eq (hcapsD m))

theorem hfamH_site (hg : 0 < gamma) (hh : gamma < 1/2) (ph : Phase)
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
    (hk : k = ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    (hr : r = SourceSteps.rBsel sources p)
    (hLe : L = 𝔏𝔖) (hRce : Rc = ℜ𝔖) (hRke : Rk = 16 * (Rc + 1)) (hbe : b = C10PartsSchedule.entryWidthSchedule sources k r n)
    (hVe : V = SourceBudget.Params.VvOf selector sources p 𝔏𝔖 (C10PartsSchedule.widthAt sources k n))
    (hcWe : cW = Rc) (hcQe : cQ = Rc) (hcBe : cB = Rc) (hcSe : cS = Rc)
    (hcapsD : ∀ m, (capsAt m).descriptorReserve = V) (hDwe : Dw = NearCubicWires.SourceConstruction.InitRun.D0 b)
    (hrefill : refillCost = NearCubicWires.SourceFactorSel.ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hNe : N = (SourceSkeleton.phaseE sources p den k x bits modeC ph L ci).length)
    (hlayD : ∀ j, (lay j).degree = Admission.uniformDeg vQ L)
    (hon : siteOnGF mask packets rows sources p hg hh den hden ≤ n) :
    ∀ j, j < N → ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))) (layA (j+1)) (factsA (j+1))) vWS vRW vBF (dataList (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))) (layA (j+1)) (factsA (j+1))).length i + (fuelOf 𝒞 b vdX (j+1)) + 1 ≤ Rc := by
  unfold siteOnGF at hon
  simp only [max_le_iff] at hon
  obtain ⟨-, o2, -, -, -⟩ := hon
  exact hfamH_RP mask packets rows sources res hres p k r hg hh ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay
    capsAt goodAt K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N
    (clock_of mask packets rows sources p hg hh k hk) (hfamOn_of mask packets rows sources p hg hh k hk n _ o2) hr hLe hRce hbe hVe hDwe hlayD

theorem seamRows_site (hg : 0 < gamma) (hh : gamma < 1/2) (ph : Phase)
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
    (hk : k = ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    (hr : r = SourceSteps.rBsel sources p)
    (hLe : L = 𝔏𝔖) (hRce : Rc = ℜ𝔖) (hRke : Rk = 16 * (Rc + 1)) (hbe : b = C10PartsSchedule.entryWidthSchedule sources k r n)
    (hVe : V = SourceBudget.Params.VvOf selector sources p 𝔏𝔖 (C10PartsSchedule.widthAt sources k n))
    (hcWe : cW = Rc) (hcQe : cQ = Rc) (hcBe : cB = Rc) (hcSe : cS = Rc)
    (hcapsD : ∀ m, (capsAt m).descriptorReserve = V) (hDwe : Dw = NearCubicWires.SourceConstruction.InitRun.D0 b)
    (hrefill : refillCost = NearCubicWires.SourceFactorSel.ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hNe : N = (SourceSkeleton.phaseE sources p den k x bits modeC ph L ci).length)
    (hlayD : ∀ j, (lay j).degree = Admission.uniformDeg vQ L)
    (hon : siteOnGF mask packets rows sources p hg hh den hden ≤ n)
    (hY : ∀ j, j < N → ((SourceSkeleton.ClassV4.siteY4 selector mask packets rows).at sources gamma hg hh p 𝔏𝔖 k).In 4 𝔏𝔖 n
      (C10PartsSchedule.widthAt sources k n)
      (Rest.restCost se sp (fun _ => 0) (requestAt coordC ph ci L tgtC modeC (j+1)) 0 b vQ
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length
          vMB vMS j +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1))
          (layA (j+1)) (factsA (j+1)) (capsAt (j+1))
          (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length
            then vMB else vMS) vU0 vWS vRW vBF b 0))     (hG : ∀ j, j < N → g7cost (j+1) ≤ RuntimeShape.tableClass 𝔏𝔖 0 (C10PartsSchedule.widthAt sources k n)) :
    (∀ j, j < N → cursorCost j + 1 + g7cost (j+1) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b (0)) + 1 ≤ Rc) ∧
    (∀ j, j < N → (restCost se sp g7cost (requestAt coordC ph ci L tgtC modeC (j+1)) Rc b vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b (0)) + 1 ≤ Rk) ∧
    (∀ j, j < N → (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b ((4*Rk+7) + 1 + ((4*Rc+7) + 1 + ((restCost se sp g7cost (requestAt coordC ph ci L tgtC modeC (j+1)) Rc b vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j) + 1 + refreshCost Rc)))) ≤ refillCost) := by
  unfold siteOnGF at hon
  simp only [max_le_iff] at hon
  obtain ⟨-, -, -, -, o5⟩ := hon
  exact NearCubicWires.SourceFactorSel.ClauseCost.seamRows selector mask packets rows sources gamma hg hh p
    (SourceBudget.capIndexOf (ParamsV4.den0W selector mask packets rows)) se sp g7cost (requestAt coordC ph ci L tgtC modeC)
    (fun m => layA m) (fun m => factsA m) capsAt b vQ vMB vMS vU0 vWS vRW vBF N k n Rc Rk refillCost hk o5 hRce hRke hrefill hY hG

/-- The layout rows at the site. -/
theorem layRows_site (hg : 0 < gamma) (hh : gamma < 1/2) (ph : Phase)
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
    (hk : k = ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    (hr : r = SourceSteps.rBsel sources p)
    (hLe : L = 𝔏𝔖) (hRce : Rc = ℜ𝔖) (hRke : Rk = 16 * (Rc + 1)) (hbe : b = C10PartsSchedule.entryWidthSchedule sources k r n)
    (hVe : V = SourceBudget.Params.VvOf selector sources p 𝔏𝔖 (C10PartsSchedule.widthAt sources k n))
    (hcWe : cW = Rc) (hcQe : cQ = Rc) (hcBe : cB = Rc) (hcSe : cS = Rc)
    (hcapsD : ∀ m, (capsAt m).descriptorReserve = V) (hDwe : Dw = NearCubicWires.SourceConstruction.InitRun.D0 b)
    (hrefill : refillCost = NearCubicWires.SourceFactorSel.ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hNe : N = (SourceSkeleton.phaseE sources p den k x bits modeC ph L ci).length)
    (hlayD : ∀ j, (lay j).degree = Admission.uniformDeg vQ L)
    (hon : siteOnGF mask packets rows sources p hg hh den hden ≤ n) :
    1 ≤ L ∧ 1 ≤ vQ / (200 * (normalizedLiveCount vQ L + 1 + 1)) := by
  unfold siteOnGF at hon
  simp only [max_le_iff] at hon
  obtain ⟨-, -, o3, o4, -⟩ := hon
  have o4' : (SourceSteps.selR sources p k).onset ≤ n := by rw [hk]; exact o4
  have hcut := SourceSteps.selR_cutoff sources p k o4'
  have hu0 := (NearCubicWires.SourceStart.LayRP.layOnW_spec selector mask packets rows sources gamma hg hh p n o3).2
  refine ⟨?_, NearCubicWires.SourceStart.LayRP.hu_of sources p k n x bits L hcut ?_⟩
  · rw [hLe]
    unfold SourceSkeleton.ClassV4.siteL4 SourceBudget.liveOfR
    omega
  · rw [hLe, hk]; exact hu0

theorem seamNums_site (hg : 0 < gamma) (hh : gamma < 1/2) (ph : Phase)
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
    (hk : k = ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    (hr : r = SourceSteps.rBsel sources p)
    (hLe : L = 𝔏𝔖) (hRce : Rc = ℜ𝔖) (hRke : Rk = 16 * (Rc + 1)) (hbe : b = C10PartsSchedule.entryWidthSchedule sources k r n)
    (hVe : V = SourceBudget.Params.VvOf selector sources p 𝔏𝔖 (C10PartsSchedule.widthAt sources k n))
    (hcWe : cW = Rc) (hcQe : cQ = Rc) (hcBe : cB = Rc) (hcSe : cS = Rc)
    (hcapsD : ∀ m, (capsAt m).descriptorReserve = V) (hDwe : Dw = NearCubicWires.SourceConstruction.InitRun.D0 b)
    (hrefill : refillCost = NearCubicWires.SourceFactorSel.ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hNe : N = (SourceSkeleton.phaseE sources p den k x bits modeC ph L ci).length)
    (hlayD : ∀ j, (lay j).degree = Admission.uniformDeg vQ L)
    (hon : siteOnGF mask packets rows sources p hg hh den hden ≤ n)
    (hY : ∀ j, j < N → ((SourceSkeleton.ClassV4.siteY4 selector mask packets rows).at sources gamma hg hh p 𝔏𝔖 k).In 4 𝔏𝔖 n
      (C10PartsSchedule.widthAt sources k n)
      (Rest.restCost se sp (fun _ => 0) (requestAt coordC ph ci L tgtC modeC (j+1)) 0 b vQ
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length
          vMB vMS j +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1))
          (layA (j+1)) (factsA (j+1)) (capsAt (j+1))
          (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length
            then vMB else vMS) vU0 vWS vRW vBF b 0))     (hG : ∀ j, j < N → g7cost (j+1) ≤ RuntimeShape.tableClass 𝔏𝔖 0 (C10PartsSchedule.widthAt sources k n))     (hKpos : ∀ x, K x → x.val < (𝔇).F ∨ ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e 𝒽 10 ∧ x ≠ Dims.hrT e 𝒽 11))
    (hKpad : ∀ x, K x → (𝔇).F ≤ x.val → ZeroPadding.pad Rc (K0 x) = K0 x)
    (hKapp : ∀ x, K x → ∀ i, (𝒞).app i ≠ x)
    (hKfree : ∀ x, K x → Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽) (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) x ∨ x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1 ∨ x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2)
    (hKr1 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) → K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = List.replicate (capsAt (j+1)).descriptorReserve true ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = 0)
    (hKr2 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) → K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = List.replicate (capsAt (j+1)).descriptorReserve false ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = 0) :     SeamNums mask packets rows sources res hres p k r ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay capsAt goodAt
      K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N := by
  have R := seamRP_site mask packets rows sources res p k r hg hh ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay capsAt goodAt K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N hk hr hLe hRce hRke hbe hVe hcWe hcQe hcBe hcSe hcapsD hDwe hrefill hNe hlayD hon
  have hF := hfamH_site mask packets rows sources res hres p k r hg hh ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay capsAt goodAt K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N hk hr hLe hRce hRke hbe hVe hcWe hcQe hcBe hcSe hcapsD hDwe hrefill hNe hlayD hon
  have hS := seamRows_site mask packets rows sources res p k r hg hh ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay capsAt goodAt K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N hk hr hLe hRce hRke hbe hVe hcWe hcQe hcBe hcSe hcapsD hDwe hrefill hNe hlayD hon hY hG
  have hLy := layRows_site mask packets rows sources res p k r hg hh ph se sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay capsAt goodAt K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N hk hr hLe hRce hRke hbe hVe hcWe hcQe hcBe hcSe hcapsD hDwe hrefill hNe hlayD hon
  exact
    { hlay := hlayD, hL1 := hLy.1, hu := hLy.2,
      hRk := R.hRk, hcW := R.hcW, hcQ := R.hcQ, hcB := R.hcB, hcS := R.hcS, hSl := R.hSl, hRl := R.hRl, hBl := R.hBl, h4b := R.h4b,
      hUl := R.hUl, hMb := R.hMb, hMs := R.hMs,
      hKpos := hKpos, hKpad := hKpad, hKapp := hKapp, hKfree := hKfree, hKr1 := hKr1, hKr2 := hKr2,
      hj := R.hj, hRc := R.hRc, hlog := R.hlog, he1 := R.he1, hpw := R.hpw, hfirst := R.hfirst, hsecond := R.hsecond, hdescR := R.hdescR,
      hL := R.hL, hfamH := hF, hwinI := hS.1, hwinZ := hS.2.1, hcost := hS.2.2 }

end nums

end
end NearCubicWires.SourceFactorSel.SeamSiteGF
end

