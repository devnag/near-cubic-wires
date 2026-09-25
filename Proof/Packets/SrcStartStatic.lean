import Proof.Packets.SrcLayRows
import Proof.Packets.SrcSeamFamH
import Proof.SourceAssembly.SourceSkelStartC

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
namespace NearCubicWires.SourceStart.StartRP
open NearCubicWires.SourceSkeleton.KeptW NearCubicWires.SourceSkeleton.GuardG NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge NearCubicWires.SourceSteps
open PCJ515eaa990d75455b_FamilyInit
noncomputable section

theorem qword_le_capC (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k n : Nat) (x : BitInput n) (bits : List Bool)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) :
    (SourceSteps.qwordAt sources p k n x bits ci.val).length ≤
      capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) := by
  unfold SourceSteps.qwordAt
  rw [dif_pos ci.isLt]
  obtain ⟨rc, hrun, hsteps, h15⟩ := RepairOrdinary.PCPPQueryClause.lookup_run
    (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
    ((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) ci
  have hlen := RepairOrdinary.DecompositionSource.one_tape_support _ _ _ rc 15 0 hrun (by rfl) (by rfl)
  rw [h15] at hlen
  have hcap := RepairOrdinary.PCPPQueryCachedBounds.clause_capacity (CloseoutLanguage.selectedPCPP sources)
    (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) ci
  have h2 := le_trans hlen (by omega : 0 + rc.steps ≤ RepairOrdinary.PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources)
    ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size +
      (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity))
  exact h2

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

structure StartStaticRP (G7 : FirstW.G7W selector xtra)
    (hres : 19 ≤ 𝔯𝔢𝔰)
    (ph : Phase)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) s)
    (compiler : Packets.CompilerLaws)
    (den : Nat)
    (hden : 0 < den)
    (n : Nat)
    (x : BitInput n)
    (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p 𝔨 𝔯 𝔰) states)
    (ci : Fin (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC))
    (lay : TraceData.LayoutFamily coordC ph ci sources 𝔏 tgtC modeC selector)
    (dflt : P1TopDownPaidReusable.Datum)
    (Hd : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Nat)
    (Ad : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → List Bool)
    (familyCost firstCost counterReserve refillCost : Nat)
    (capsAt : ℕ → RowCaps) : Prop where
  hRk : ℜ ≤ (InitS.Rk ℜ)
  hRc4 : 4 ≤ ℜ
  hSl : vWS + 2 ≤ ℜ
  hRl : vRW + 2 ≤ ℜ
  hBl : vBF + 2 ≤ ℜ
  hvl : 𝔟 + 2 ≤ ℜ
  hUl : vU0 ≤ ℜ
  hMb : vMB ≤ ℜ
  hMs : vMS ≤ ℜ
  hN : (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordC ph ci).length).length ≤ ℜ
  hlog : 2 * ((requestAt coordC ph ci 𝔏 tgtC modeC 0).input (decompositionOf sources)).length + 1 ≤ ℜ
  he1 : 1 ≤ (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0)
  hpw : (CloseoutRowsCountBinary.bits ((PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0))).length ≤ 𝔟
  hfirst : (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * 2^(natBitLength ((PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0))) < 2^𝔟
  hsecond : (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * 2^(vQ+1) < 2^𝔟
  hdescR : (capsAt 0).descriptorReserve ≤ ℜ
  hL : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length + 3 ≤ ℜ
  hfamH0 : ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC 0)) (layA 0) (factsA 0)) vWS vRW vBF (dataList (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC 0)) (layA 0) (factsA 0)).length i + (fuelOf 𝒞 𝔟 vdS0 0) + 1 ≤ ℜ
  hlay : ∀ j, (lay j).degree = Admission.uniformDeg vQ 𝔏
  hL1 : 1 ≤ 𝔏
  hu : 1 ≤ vQ / (200 * (normalizedLiveCount vQ 𝔏 + 1 + 1))
  hqw : (SourceSteps.qwordAt sources p 𝔨 n x bits ci.val).length ≤ 𝔠𝔞𝔭
  h4b : 4 * 𝔟 + 5 ≤ ℜ

theorem startStatic_site (G7 : FirstW.G7W selector xtra)
    (hres : 19 ≤ 𝔯𝔢𝔰)
    (ph : Phase)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) s)
    (compiler : Packets.CompilerLaws)
    (den : Nat)
    (hden : 0 < den)
    (n : Nat)
    (x : BitInput n)
    (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p 𝔨 𝔯 𝔰) states)
    (ci : Fin (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC))
    (lay : TraceData.LayoutFamily coordC ph ci sources 𝔏 tgtC modeC selector)
    (dflt : P1TopDownPaidReusable.Datum)
    (Hd : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Nat)
    (Ad : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → List Bool)
    (familyCost firstCost counterReserve refillCost : Nat)
    (capsAt : ℕ → RowCaps)
    (hext : extraW selector xtra mask packets rows sources gamma hg hh p ≤ n)
    (hsOn : NearCubicWires.SourceStart.SeamRP.seamOnW selector mask packets rows sources gamma hg hh p ≤ n)
    (hfOn : NearCubicWires.SourceStart.SeamRP.hfamOnW selector mask packets rows sources gamma hg hh p ≤ n)
    (hlo : NearCubicWires.SourceStart.LayRP.layOnW selector mask packets rows sources gamma hg hh p ≤ n)
    (hdenE : den = (fPW selector xtra mask packets rows).capIndex sources gamma hg hh p + 1)
    (hlayD : ∀ j, (lay j).degree = Admission.uniformDeg vQ 𝔏)
    (hcaps0 : (capsAt 0).descriptorReserve ≤ 𝔙) :
    StartStaticRP selector xtra mask packets rows sources gamma hg hh p G7 hres ph g7F compiler den hden n x bits hp site ci lay dflt Hd Ad
      familyCost firstCost counterReserve refillCost capsAt := by
  have hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n :=
    (NearCubicWires.SourceStart.LayRP.layF_adm selector mask packets rows sources gamma hg hh p xtra n hext).1
  have hvq : vQ = 𝔮 := Admission.req_arity sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x _ hcut
  have hs := NearCubicWires.SourceStart.SeamRP.seamOn_site selector mask packets rows sources gamma hg hh p xtra n hsOn
  unfold NearCubicWires.SourceStart.SeamRP.seamOn at hs
  simp only [max_le_iff] at hs
  obtain ⟨n1, n2, n3, n4⟩ := hs
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    Classical.choose_spec (ClassV4.seam_scalars_Rc4 selector mask packets rows sources gamma hg hh p 𝔨) n n1
  have hcall := Classical.choose_spec (ClassV4.seam_call_Rc4 selector mask packets rows sources gamma hg hh p 𝔨
    ((fPW selector xtra mask packets rows).capIndex sources gamma hg hh p + 1) (Nat.succ_pos _)) n n2
  have hq0 := Classical.choose_spec (SourceBudget.widthAt_ge_eventually sources 𝔨
    (Classical.choose (SourceSteps.enc_sat_at sources 𝔨 (SourceSteps.rBsel sources p) (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)))) n n3
  have h4b : 4 * 𝔟 + 5 ≤ ℜ := Classical.choose_spec (SourceSteps.enc_sat_at sources 𝔨 (SourceSteps.rBsel sources p)
    (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)) n hq0 1 (hRx4 selector mask packets rows sources gamma hg hh p) le_rfl
  obtain ⟨hadm, hqr, hLr⟩ := SourceSteps.site_call_facts sources p den hden 𝔨 𝔯 𝔰 n x bits hp ph ci 𝔏 hden hcut 0
  have hadm' : Admission.RequestAdmitted ((fPW selector xtra mask packets rows).capIndex sources gamma hg hh p + 1) p.clauseDegree
      (SourceBudget.tgt sources p) (requestAt coordC ph ci 𝔏 tgtC modeC 0) := hdenE ▸ hadm
  have hc0 := hcall _ hadm' hLr hqr
  -- the entry count
  have hNm := NearCubicWires.SourceStart.SeamRP.phaseE_len_monomials sources p den 𝔨 x bits modeC ph 𝔏 ci
  have hNb := NearCubicWires.SourceStart.SeamRP.phaseE_len_le_b sources p den 𝔨 (SourceSteps.selR sources p 𝔨) n4 x bits modeC ph 𝔏 ci
  -- hfamH0's class and fuel
  have hfam := NearCubicWires.SourceStart.SeamRP.hfamOn_site selector mask packets rows sources gamma hg hh p xtra n hfOn
  unfold NearCubicWires.SourceStart.SeamRP.hfamOn at hfam
  simp only [max_le_iff] at hfam
  obtain ⟨m1, m2⟩ := hfam
  have hdeg : ∀ j, degOf sources selector coordC ph ci 𝔏 tgtC modeC lay j ≤ C10PartsSchedule.widthAt sources 𝔨 n := fun j =>
    (SourceSteps.degOf_le_arity selector sources p den hden 𝔨 𝔯 𝔰 n x bits hp ph ci 𝔏 lay hlayD j).trans (le_of_eq hvq)
  have hb1 : 1 ≤ 𝔟 := by
    unfold C10PartsSchedule.entryWidthSchedule C10PartsSchedule.widthPower
    have := Nat.one_le_pow 𝔯 (C10PartsSchedule.widthAt sources 𝔨 n + 1) (Nat.succ_pos _)
    omega
  have hDw : InitRun.D0 𝔟 + 1 ≤ 22 * (C10PartsSchedule.entryWidthSchedule sources 𝔨 (SourceSteps.selR sources p 𝔨).exponent n + 1) := by
    show InitRun.D0 𝔟 + 1 ≤ 22 * (𝔟 + 1)
    unfold InitRun.D0 InitEnc.rr
    omega
  refine
    { hRk := by unfold InitS.Rk; omega
      hRc4 := by omega
      hSl := a1
      hRl := a2
      hBl := a3
      hvl := by omega
      hUl := by rw [hvq]; exact a5
      hMb := by rw [hvq]; exact a6
      hMs := by rw [hvq]; exact a7
      hN := by
        simp only [RepairSource.VerifierDecoding.CompareMachine.word, List.length_cons, List.length_replicate]
        have hNb' : (monomials coordC ph ci).length ≤ 𝔟 := hNm ▸ hNb
        omega
      hlog := hc0.1
      he1 := SourceSteps.seedCount_pos _ _
      hpw := SourceSteps.f6_hpw sources p den hden 𝔨 𝔯 𝔰 n x bits hp ph ci 𝔏 (SourceSteps.selR sources p 𝔨) n4 rfl 0
      hfirst := SourceSteps.f6_hfirst sources p den hden 𝔨 𝔯 𝔰 n x bits hp ph ci 𝔏 (SourceSteps.selR sources p 𝔨) n4 rfl 0
      hsecond := SourceSteps.f6_hsecond sources p den hden 𝔨 𝔯 𝔰 n x bits hp ph ci 𝔏 (SourceSteps.selR sources p 𝔨) n4 rfl 0
      hdescR := hcaps0.trans a4
      hL := hc0.2
      hfamH0 := fun i => by
        refine Classical.choose_spec (SourceBudget.hfamH_at sources 𝔨
            (NearCubicWires.SourceStart.SeamRP.famW selector sources gamma hg hh p 𝔨) 2 𝔏 le_rfl
            (NearCubicWires.SourceStart.SeamRP.famSite_dP_le_kW selector mask packets rows sources gamma hg hh p)) n m1 _ ?_
          ((ClassV4.siteR4 selector mask packets rows).C sources gamma hg hh p) ((ClassV4.siteR4 selector mask packets rows).hR sources gamma hg hh p)
          le_rfl (NearCubicWires.SourceStart.SeamRP.famSite_hT_le selector mask packets rows sources gamma hg hh p 𝔨) _ _ _ _ _ _ i
        exact NearCubicWires.SourceStart.SeamRP.family_hcost_all sources p den 𝔨 hden (SourceSteps.selR sources p 𝔨) n4 hcut x bits modeC ph 𝔏 ci
          selector compiler lay (degOf sources selector coordC ph ci 𝔏 tgtC modeC lay) hdeg (printerOf sources) 𝔙
          (SourceBudget.Params.cVcN selector sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) le_rfl
          (InitRun.D0 𝔟) 22 hDw 2 (NearCubicWires.SourceStart.SeamRP.famW selector sources gamma hg hh p 𝔨)
          ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩ 0
      hlay := hlayD
      hL1 := one_le_LW selector mask packets rows sources gamma hg hh p
      hu := NearCubicWires.SourceStart.LayRP.hu_of sources p 𝔨 n x bits 𝔏 hcut
        (NearCubicWires.SourceStart.LayRP.layOnW_spec selector mask packets rows sources gamma hg hh p n hlo).2
      hqw := qword_le_capC sources p 𝔨 n x bits ci
      h4b := h4b }

end site

end
end NearCubicWires.SourceStart.StartRP
end

