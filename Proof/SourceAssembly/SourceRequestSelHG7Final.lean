import Proof.SourceAssembly.SourceFactorSelG7W
import Proof.SourceAssembly.SourceRequestAdmitRead
import Proof.SourceAssembly.SourceRequestSelCapS
import Proof.SourceAssembly.SourceRequestSelG7Final
import Proof.SourceAssembly.SourceRequestSelKeptSite
import Proof.SourceAssembly.SourceSkelStartC5W
import Proof.SourceAssembly.SourceStepsCallFacts

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceRequest.SelHG7Final
open NearCubicWires.SourceSkeleton.StartC
open NearCubicWires.SourceSkeleton.KeptW NearCubicWires.SourceSkeleton.GuardG NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge NearCubicWires.SourceSteps
open PCJ515eaa990d75455b_FamilyInit
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- The kept cache with word 15 blank is the query cache at the empty pair. -/
theorem cd_update (P : List Bool) (ar ci C : ℕ) (w : List Bool) (j : Fin 19) :
    Function.update (PCPPQueryIndexPadding.clauseData P ar ci C w) 15 (List.replicate C false) j =
      PCPPQueryIndexPadding.clauseData P ar ci C [] j := by
  fin_cases j <;> rfl

theorem rc_table (L h q : ℕ) : RuntimeShape.tableClass L 0 q ≤ RuntimeShape.tableClass L h q := by
  unfold RuntimeShape.tableClass
  rw [pow_zero, one_mul]
  exact Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by omega))

section site
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯𝔢𝔰" => resSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔰" => scrSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔘" => USite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯
set_option hygiene false in
local notation "𝒽1" => UOf_le_succ mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯
set_option hygiene false in
local notation "𝔮" => C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n
set_option hygiene false in
local notation "𝔏" => LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "ℜ" => Once.Rc (hRx4 selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p) 1 (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔙" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden 𝔨 𝔯 𝔰 n x bits hp
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "vQ" => (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC).arity
set_option hygiene false in
local notation "layA" => layoutAtOf sources selector coordC ph ci 𝔏 tgtC modeC lay
set_option hygiene false in
local notation "factsA" => factsAtOf sources selector compiler coordC ph ci 𝔏 tgtC modeC
set_option hygiene false in
local notation "vWS" => P1TopDownPaidReusableReserves.workspace (printerOf sources) 𝔙
set_option hygiene false in
local notation "vRW" => P1TopDownPaidReusableReserves.rewind (printerOf sources) 𝔙
set_option hygiene false in
local notation "vBF" => P1TopDownPaidReusableReserves.buffer 𝔙
set_option hygiene false in
local notation "vMB" => InitRun.Mb 𝔏 vQ
set_option hygiene false in
local notation "vMS" => InitPost.Ms 𝔏 vQ
set_option hygiene false in
local notation "vU0" => InitRun.U0 𝔏 vQ
set_option hygiene false in
local notation "ℭ𝔖" => cacheSite selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)
set_option hygiene false in
local notation "𝔔" => q284Site selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)
set_option hygiene false in
local notation "𝔟" => C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n
set_option hygiene false in
local notation "𝔠𝔞𝔭" => capC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC
set_option hygiene false in
local notation "𝔴𝔮" => ZeroPadding.pad 𝔠𝔞𝔭 (SourceSteps.qwordAt sources p 𝔨 n x bits ci.val)
set_option hygiene false in
local notation "preFF" => fun ph' => firstW selector xtra G7 mask packets rows sources gamma hg hh p modeC ph'
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph' (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "vdS0" => clauseVals mask selector packets rows compiler sources p den hden 𝔨 𝔯 𝔰 n x bits hp site codeF ph ci 𝔏 lay (degOf sources selector coordC ph ci 𝔏 tgtC modeC lay) 𝔙 dflt (InitRun.D0 𝔟) (InitRun.cap0 𝔟) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝔟) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝔟) (fun j => if j = 0 then [] else oldAt coordC ph ci sources 𝔏 tgtC modeC 𝔟 (InitRun.D0 𝔟) j) Hd Ad ℜ familyCost refillCost firstCost counterReserve
set_option hygiene false in
local notation "𝔦𝔠" => InitS.initAllXCostE (plSite selector xtra mask packets rows sources gamma hg hh p modeC ph) 𝔏 1
  (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p)
  (rC sources gamma hg hh p) (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1 (ldE sources gamma hg hh p)
  (ldC sources gamma hg hh p) modeC (SourceBudget.Params.tgOf sources gamma hg hh p) 𝔮 𝔟 (dE sources gamma hg hh p)
  (dC sources gamma hg hh p) (cwE sources gamma hg hh p) (cwC sources gamma hg hh p)
  (NearCubicWires.SourceStart.MetaStepGF.metaCostG selector sources p packets 𝔏 𝔮) + 2

set_option hygiene false in
local notation "𝔮𝔰" => C10PartsSchedule.widthAt sources 𝔨 n
set_option hygiene false in
local notation "MBC" => NearCubicWires.SourceStart.MetaRun.MBof selector sources p packets 𝔏 𝔮𝔰
set_option hygiene false in
local notation "PwC" => NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (𝔮𝔰 + 1) ^ NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p
set_option hygiene false in
local notation "WCq" => SourceBudget.wCap 𝔮𝔰
set_option hygiene false in
local notation "LdCq" => SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) 𝔮𝔰
set_option hygiene false in
local notation "cwidC" => NearCubicWires.SourceSkeleton.InitS.cwidOf modeC LdCq
set_option hygiene false in
local notation "cwCq" => NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p * (𝔮𝔰 + 1) ^ NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p
set_option hygiene false in
local notation "DCq" => NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p * (𝔮𝔰 + 1) ^ NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p
set_option hygiene false in
local notation "cdC" => Function.update (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) 15 (List.replicate 𝔠𝔞𝔭 false)
set_option hygiene false in
local notation "resWC" => StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟
set_option hygiene false in
local notation "NCC" => NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC
set_option hygiene false in
local notation "KKs" => KSite selector xtra mask packets rows sources gamma hg hh p V hV modeC
set_option hygiene false in
local notation "KK0s" => K0Site selector xtra mask packets rows sources gamma hg hh p V hV modeC (RepairOrdinary.frame bits) 𝔴𝔮 cdC resWC 𝔙 NCC

theorem hG7_gen (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (hon : SourceRequest.SelLoopSite.g7OnsetF selector mask packets rows sources gamma hg hh p 𝔏 tgtC (SourceBudget.tgt sources p) ≤ n)
    (ph : Phase) (ci : Fin NCC)
    (lay : TraceData.LayoutFamily coordC ph ci sources 𝔏 tgtC modeC selector) (capsAt : ℕ → RowCaps)
    (hMB : ∀ m, SLoad.Setup.metaBits (layA m).w (layA m).degree (layA m).C (capsAt m) = MBC)
    (hdR : ∀ m, (capsAt m).descriptorReserve = 𝔙)
    (V : ℕ) (hV : (𝔡).U ≤ V) :
    ResidentRunH
      (NearCubicWires.SourceFactorSel.G7Fam.g7At mask packets rows sources (NearCubicWires.SourceSkeleton.FirstW.resSite selector mask packets rows sources gamma hg hh p) p (NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p) (NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p) hV (NearCubicWires.SourceSkeleton.Params.gG7 sources gamma hg hh p)
        (fun md => NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV md) (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV)
        (NearCubicWires.SourceRequest.SelHG7Site.hresSite selector xtra mask packets rows sources gamma hg hh p) (NearCubicWires.SourceRequest.SelHG7Site.hNSite selector mask packets rows sources gamma hg hh p)
        (NearCubicWires.SourceRequest.SelHG7Site.hNSiteS selector mask packets rows sources gamma hg hh p)
        (NearCubicWires.SourceRequest.SelHG7Site.hroomSite selector mask packets rows sources gamma hg hh p (NearCubicWires.SourceFactorSel.G7Fam.kb sources) (NearCubicWires.SourceRequest.SelG7Spec.kb_le sources)) modeC ph).2
      (NearCubicWires.SourceRequest.SelG7Spec.g7costW sources mask MBC (RepairSource.CloseoutLanguage.selectedPCPP sources) (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) ci coordC bits ph 𝔏 tgtC cwidC cwCq DCq 𝔟 PwC WCq LdCq modeC)
      mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV) coordC ph ci 𝔏 tgtC modeC ℜ 𝔟
      ((𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layA capsAt
      (Dims.Rpad (d := 𝔇) (eX := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra) (pX := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra) (gW := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW) (V := V) ℜ)
      (RestIn4 (𝔇) (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW ℜ ((𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) KKs KK0s (fun _ : Fin V => (0 : ℕ)))
      (fun x => OutV (𝔇) (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW x.val)  := by
  have hden1 : 1 ≤ den := hden
  have harity : (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC).arity = 𝔮𝔰 :=
    NearCubicWires.Admission.req_arity sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC hN
  have hread := SourceRequest.AdmitRead.coordReads_site sources p den hden 𝔨 x bits 𝔯 𝔰 hp hN
  have hlen := SourceRequest.AdmitRead.hlen_site sources p den hden 𝔨 x bits hp
  have hadm := fun m (_ : m ≤ (monomials coordC ph ci).length) =>
    SourceSteps.site_call_facts sources p den hden 𝔨 𝔯 𝔰 n x bits hp ph ci 𝔏 hden1 hN m
  have w := SourceRequest.SelG7Final.g7_windows_final selector xtra mask packets rows sources gamma hg hh p 𝔏 tgtC
    (SourceBudget.tgt sources p) den n hon x bits hlen modeC ph ci hden1 hread hadm ℜ (by show _ ≤ 1 * _; rw [Nat.one_mul]; exact rc_table _ _ _)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := SourceRequest.SelKeptSite.kept_site selector xtra mask packets rows sources gamma hg hh p V hV modeC
    bits 𝔴𝔮 cdC ℜ 𝔮𝔰 𝔏 (NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p)
    1 3 (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p)
    (SourceBudget.tgt sources p) (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p) 𝔟 MBC 𝔙 NCC
  have hdw := SourceRequest.SelDWin.dwin_site sources gamma hg hh p 𝔮𝔰 modeC
  obtain ⟨hF, ho, hB, hU, hres', hx25⟩ := KeptW.site_nums selector xtra mask packets rows sources gamma hg hh p
  -- the kept words
  have hKc : ∀ j, KKs (cacheSite selector xtra mask packets rows sources gamma hg hh p V hV modeC j) ∧
      KK0s (cacheSite selector xtra mask packets rows sources gamma hg hh p V hV modeC j) =
        PCPPQueryIndexPadding.clauseData (pcppOutput (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC)
          ((RepairSource.CloseoutLanguage.selectedPCPP sources).output (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC)))
          (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC).arity ci.val 𝔠𝔞𝔭 [] j ∧
      (fun _ : Fin V => (0 : ℕ)) (cacheSite selector xtra mask packets rows sources gamma hg hh p V hV modeC j) = 0 :=
    fun j => ⟨(k1 j).1, (k1 j).2.1.trans (cd_update _ _ _ _ _ j), rfl⟩
  have hKr : ∀ i, i < 10 → ∀ y : Fin V, y.val = (𝔡).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
      (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW + i →
      KKs y ∧ KK0s y = ZeroPadding.pad ℜ ((if modeC then SourceRequest.SelLocal.resWS else SourceRequest.SelLocal.resW)
        (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC).arity PwC WCq LdCq 𝔏 tgtC cwidC cwCq i) ∧ (fun _ : Fin V => (0 : ℕ)) y = 0 := by
    intro i hi y hy
    obtain ⟨a1, a2, a3⟩ := k3 i hi y hy
    refine ⟨a1, a2.trans ?_, a3⟩
    rw [harity, Nat.one_mul]
    rfl
  have hq284 : Dims.queryCopy (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV =
      q284Site selector xtra mask packets rows sources gamma hg hh p V hV := Fin.ext rfl
  have hKq : KKs (Dims.queryCopy (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV) ∧
      KK0s (Dims.queryCopy (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV) =
        ZeroPadding.pad 𝔠𝔞𝔭 (natListWord
          [RepairRepresentation.literalIndex (((RepairSource.CloseoutLanguage.selectedPCPP sources).output (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC)).clauses ci).left,
           RepairRepresentation.literalIndex (((RepairSource.CloseoutLanguage.selectedPCPP sources).output (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC)).clauses ci).right]) ∧
      (fun _ : Fin V => (0 : ℕ)) (Dims.queryCopy (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV) = 0 := by
    refine ⟨?_, ?_, rfl⟩
    · rw [hq284]; exact Or.inl (Or.inr (Or.inl rfl))
    · rw [hq284, K0Site_284]
      show ZeroPadding.pad 𝔠𝔞𝔭 (SourceSteps.qwordAt sources p 𝔨 n x bits ci.val) = _
      unfold SourceSteps.qwordAt
      rw [dif_pos ci.isLt]
  have hKres : ∀ m, m ≤ (monomials coordC ph ci).length → ∀ y : Fin V,
      (𝔡).B + 43 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra
        (DSite selector mask packets rows sources gamma hg hh p).gW ≤ y.val →
      y.val < (𝔡).B + 48 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra
        (DSite selector mask packets rows sources gamma hg hh p).gW →
      KKs y ∧ KK0s y = ZeroPadding.pad ℜ (NearCubicWires.SourceFactorSel.Words.wd (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC m) MBC
        (y.val - ((𝔡).B + 43 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra
          (DSite selector mask packets rows sources gamma hg hh p).gW) + 6)) ∧ (fun _ : Fin V => (0 : ℕ)) y = 0 := by
    intro m hm y hy1 hy2
    obtain ⟨-, hqm, hL⟩ := hadm m hm
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))), ?_, rfl⟩
    rw [KeptW.K0Site_strip selector xtra mask packets rows sources gamma hg hh p V hV modeC _ _ _ _ 𝔙 NCC y (by omega)]
    have hi : y.val - ((𝔡).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
        (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW) =
      (y.val - ((𝔡).B + 43 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
        (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW)) + 14 := by omega
    rw [hi]
    have hj5 : y.val - ((𝔡).B + 43 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
        (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW) < 5 := by omega
    generalize y.val - ((𝔡).B + 43 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
        (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW) = j at hj5 ⊢
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj with h | h | h | h | h <;> subst h <;>
      simp only [StartGuard.resWSite, NearCubicWires.SourceSkeleton.InitS.initResVal, NearCubicWires.SourceSkeleton.InitS.slotVal,
        NearCubicWires.SourceSkeleton.InitS.valAllX, NearCubicWires.SourceSkeleton.InitS.valAll, NearCubicWires.SourceFactorSel.Words.wd,
        PCJc4297ab269d8423a_Source.maskData, hqm, hL, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false] <;> rfl
  have hKrw := K0Site_rew selector xtra mask packets rows sources gamma hg hh p V hV modeC (RepairOrdinary.frame bits) 𝔴𝔮 cdC resWC 𝔙 NCC
  have hcap := SourceRequest.SelCapS.hcap_site sources gamma hg hh p 𝔨 (PolynomialClock.ordinaryClock 𝔨) den x oracleC bits hN hden1 modeC
  simp only [harity] at hcap
  exact SourceRequest.SelG7Spec.g7Spec selector xtra mask packets rows sources gamma hg hh p modeC hV
    (RepairSource.CloseoutLanguage.selectedPCPP sources) (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) coordC ph ci 𝔏 tgtC ℜ 𝔟 𝔠𝔞𝔭
    layA capsAt MBC 𝔙 KKs KK0s (fun _ : Fin V => (0 : ℕ)) PwC WCq LdCq bits hread cwidC cwCq DCq
    (20 * SourceRequest.SelWinSite.sqS selector xtra mask packets rows sources gamma hg hh p 𝔏 tgtC (SourceBudget.tgt sources p) 𝔮𝔰 + 50) 0 []
    hKc k2 hKr k4 k5 k6 w.hc w.hwinA w.hQR w.hiL w.hiR w.hcL w.hcR w.hbig rfl hdw.2.2.2.2 w.hwinR (by rw [harity]; exact hdw.1)
    hdw.2.1 hdw.2.2.1 hdw.2.2.2.1 w.hDR w.hDC w.hHfit
    (Nat.mul_pos (SourceRequest.SelWinSite.cwC_pos sources gamma hg hh p) (Nat.one_le_pow _ _ (by omega)))
    (SourceRequest.SelCoefV.hcoef_site sources 𝔨 p den n x bits _ (NearCubicWires.SourceSkeleton.Params.coefficientAt_le_cw sources gamma hg hh p 𝔮𝔰))
    (SourceRequest.SelCoefV.VbF sources 𝔨 p n) (SourceRequest.SelCoefV.four_le_VbF sources 𝔨 p n)
    (SourceRequest.SelCoefV.hcoefV_site sources 𝔨 p den n x bits) w.hbigR hcap w.hRc1 hKq hKres
    ⟨Or.inr (Or.inl rfl), hKrw.1, rfl, Or.inr (Or.inr (Or.inl rfl)), hKrw.2, rfl⟩ hMB hdR
    w.hNw w.hS w.hT w.cq w.ck w.cm w.ci' w.hneed w.cl1 w.cl2 w.hwin

theorem hG7_seam (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (hon : SourceRequest.SelLoopSite.g7OnsetF selector mask packets rows sources gamma hg hh p 𝔏 tgtC (SourceBudget.tgt sources p) ≤ n)
    (ph : Phase) (ci : Fin NCC)
    (lay : TraceData.LayoutFamily coordC ph ci sources 𝔏 tgtC modeC selector) (capsAt : ℕ → RowCaps)
    (hMB : ∀ m, SLoad.Setup.metaBits (layA m).w (layA m).degree (layA m).C (capsAt m) = MBC)
    (hdR : ∀ m, (capsAt m).descriptorReserve = 𝔙) :
    ResidentRunH
      (FirstW.g7OfW selector xtra (NearCubicWires.SourceFactorSel.G7W.G7Site selector xtra) mask packets rows sources gamma hg hh p modeC ph).2
      (NearCubicWires.SourceRequest.SelG7Spec.g7costW sources mask MBC (RepairSource.CloseoutLanguage.selectedPCPP sources) (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) ci coordC bits ph 𝔏 tgtC cwidC cwCq DCq 𝔟 PwC WCq LdCq modeC)
      mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯)) ((𝔇).pslots (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯)) ((𝔇).slot (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯)) ((𝔇).ret (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯)) ((𝔇).scr (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) 0) ((𝔇).scr (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) 1)
      ((𝔇).familySlots (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯)) ((𝔇).poolSlots (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯)) (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯))
      ((𝔇).scr (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) 5) ((𝔇).scr (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) 6) ((𝔇).scr (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) 7) ((𝔇).scr (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) 8) ((𝔇).scr (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) 9) ((𝔇).scr (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) 10)
      (Dims.lenTape (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯)) coordC ph ci 𝔏 tgtC modeC ℜ 𝔟
      ((𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layA capsAt
      (Dims.Rpad (d := 𝔇) (eX := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra) (pX := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra) (gW := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW) (V := (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯)) ℜ)
      (RestIn4 (𝔇) (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW ℜ ((𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) ⟨64, by unfold restPc; omega⟩) (KSite selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) modeC) (K0Site selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) modeC (RepairOrdinary.frame bits) 𝔴𝔮 cdC resWC 𝔙 NCC) (fun _ : Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) => (0 : ℕ)))
      (fun x => OutV (𝔇) (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW x.val)  :=
  hG7_gen selector xtra mask packets rows sources gamma hg hh p den hden n x bits hp hN hon ph ci lay capsAt hMB hdR _ _

theorem hG7_first (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (hon : SourceRequest.SelLoopSite.g7OnsetF selector mask packets rows sources gamma hg hh p 𝔏 tgtC (SourceBudget.tgt sources p) ≤ n)
    (ph : Phase) (ci : Fin NCC)
    (lay : TraceData.LayoutFamily coordC ph ci sources 𝔏 tgtC modeC selector) (capsAt : ℕ → RowCaps)
    (hMB : ∀ m, SLoad.Setup.metaBits (layA m).w (layA m).degree (layA m).C (capsAt m) = MBC)
    (hdR : ∀ m, (capsAt m).descriptorReserve = 𝔙) :
    ResidentRunH
      (NearCubicWires.SourceFactorSel.G7W.G7Site selector xtra mask packets rows sources gamma hg hh p modeC ph (𝔘 + 1) (Nat.le_succ _)).2
      (NearCubicWires.SourceRequest.SelG7Spec.g7costW sources mask MBC (RepairSource.CloseoutLanguage.selectedPCPP sources) (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) ci coordC bits ph 𝔏 tgtC cwidC cwCq DCq 𝔟 PwC WCq LdCq modeC)
      mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots 𝒽1) ((𝔇).pslots 𝒽1) ((𝔇).slot 𝒽1) ((𝔇).ret 𝒽1) ((𝔇).scr 𝒽1 0) ((𝔇).scr 𝒽1 1)
      ((𝔇).familySlots 𝒽1) ((𝔇).poolSlots 𝒽1) (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1)
      ((𝔇).scr 𝒽1 5) ((𝔇).scr 𝒽1 6) ((𝔇).scr 𝒽1 7) ((𝔇).scr 𝒽1 8) ((𝔇).scr 𝒽1 9) ((𝔇).scr 𝒽1 10)
      (Dims.lenTape (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1) coordC ph ci 𝔏 tgtC modeC ℜ 𝔟
      ((𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layA capsAt
      (Dims.Rpad (d := 𝔇) (eX := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra) (pX := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra) (gW := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW) (V := (𝔘 + 1)) ℜ)
      (RestIn4 (𝔇) (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW ℜ ((𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨64, by unfold restPc; omega⟩) (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) ((K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val)) (fun _ : Fin (𝔘 + 1) => (0 : ℕ)))
      (fun x => OutV (𝔇) (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW x.val)  := by
  have hK0 : K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val =
      K0Site selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC (RepairOrdinary.frame bits) 𝔴𝔮 cdC resWC 𝔙 NCC :=
    funext (fun y => K0W'_eq_K0Site selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val y)
  rw [hK0]
  exact hG7_gen selector xtra mask packets rows sources gamma hg hh p den hden n x bits hp hN hon ph ci lay capsAt hMB hdR _ _

end site

end
end NearCubicWires.SourceRequest.SelHG7Final
end
