import Proof.SourceAssembly.SourceFactorSelTraceSite
import Proof.SourceAssembly.SourceRequestSelKeptNums
import Proof.SourceAssembly.SourceRequestSelStripLen
import Proof.SourceAssembly.SourceSkelFinalClose2
import Proof.SourceAssembly.SourceSkelSiteResid
import Proof.SourceAssembly.SourceStepsSeam6

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSkeleton
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
namespace NearCubicWires.SourceSkeleton.Final
open NearCubicWires.SourceSteps
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
noncomputable section

section fields
variable (selector : CyclicChoice.Laws)

set_option hygiene false in
local notation "CODE" => skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows)
  (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows))
  (ParamsV4.fPW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows)
  (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _
    (FirstW.g7OfW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows)) (FirstW.firstW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows)
set_option hygiene false in
local notation "𝔉" => forcedChoices mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows)
set_option hygiene false in
local notation "denI" => (𝔉).capIndex sources gamma hg hh p + 1
set_option hygiene false in
local notation "kI" => kSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "rI" => rSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "resI" => resSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "modeI" => PCJ374c44bb8b7f47d9_.S.mode sources p (denI) (Nat.succ_pos _) kI rI (scrSite selector mask packets rows sources gamma hg hh p) n x bits hp
set_option hygiene false in
local notation "oracleI" => C10TotalDecode.oracleOf sources kI (PolynomialClock.ordinaryClock kI) p.degree n bits
set_option hygiene false in
local notation "coordI" => PCJd04de0277f804fcc_.coordinate sources kI (PolynomialClock.ordinaryClock kI) p (denI) x oracleI bits
set_option hygiene false in
local notation "tgtI" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "LI" => ParamsV4.LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "UI" => UOf mask packets rows sources resI p kI rI
set_option hygiene false in
local notation "NCI" => NC sources kI (PolynomialClock.ordinaryClock kI) x oracleI
set_option hygiene false in
local notation "RcI" => Once.Rc (ClassV4.hRx4 selector mask packets rows sources gamma hg hh p) LI 1 (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "VI" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass LI (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "bI" => C10PartsSchedule.entryWidthSchedule sources kI rI n
set_option hygiene false in
local notation "seI" => (DSite selector mask packets rows sources gamma hg hh p).se
set_option hygiene false in
local notation "spI" => (DSite selector mask packets rows sources gamma hg hh p).sp
set_option hygiene false in
local notation "eI" => eSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "hresI" => resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows) sources gamma hg hh p
set_option hygiene false in
local notation "g7FI" => fun ph' => FirstW.g7OfW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "preFFI" => fun ph' => FirstW.firstW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "siteI" => (CODE).site sources gamma hg hh p
set_option hygiene false in
local notation "EtI" => EWFam selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows (CODE) sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "EFI" => EFSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "SFI" => ParamsV4.sfPW selector mask packets rows sources gamma hg hh p n x bits ph
set_option hygiene false in
local notation "KI" => KeptW.KSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI
set_option hygiene false in
local notation "KH0I" => (fun (_ : Fin UI) => (0 : Nat))
set_option hygiene false in
local notation "𝒞I" => skelCodeR mask packets rows sources resI hresI p kI rI ph (refill3 mask packets rows sources resI p kI rI seI spI eI (g7FI ph).2) (preFFI ph)

set_option hygiene false in
local notation "𝔛" => NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector
set_option hygiene false in
local notation "vQI" => (req sources kI (PolynomialClock.ordinaryClock kI) x oracleI).arity
set_option hygiene false in
local notation "capCI" => capC sources kI (PolynomialClock.ordinaryClock kI) x oracleI
set_option hygiene false in
local notation "BTSI" => ControllerSelectedContinuation.bodyTapes sources p kI rI (scratchOf mask packets rows sources resI)

open NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open PCJ515eaa990d75455b_FamilyInit

set_option hygiene false in
local notation "𝔇I" => dimsOf mask packets rows sources resI p kI rI
set_option hygiene false in
local notation "𝒽I" => UOf_le mask packets rows sources resI p kI rI
set_option hygiene false in
local notation "codeFI" => fun ph' => skelCodeR mask packets rows sources resI hresI p kI rI ph' (refill3 mask packets rows sources resI p kI rI seI spI eI (g7FI ph').2) (preFFI ph')
set_option hygiene false in
local notation "layI" => layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci
set_option hygiene false in
local notation "K0I" => K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci
set_option hygiene false in
local notation "dfltI" => dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph
set_option hygiene false in
local notation "costI" => costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph
set_option hygiene false in
local notation "oldI" => (fun j => if j = 0 then (A ((𝒞I).whole (Dims.encT (d := dimsOf mask packets rows sources resI p kI rI) (UOf_le mask packets rows sources resI p kI rI) 5).castSucc)).take (InitRun.D0 bI)
  else oldAt coordI ph ci sources LI tgtI modeI bI (InitRun.D0 bI) j)
set_option hygiene false in
local notation "HdZI" => (fun (_ : Nat) (_ : Fin UI) => (0 : Nat))
set_option hygiene false in
local notation "AdZI" => (fun (_ : Nat) (_ : Fin UI) => ([] : List Bool))
set_option hygiene false in
local notation "vdI" => clauseVals mask selector packets rows compiler sources p (denI) (Nat.succ_pos _) kI rI (scratchOf mask packets rows sources resI) n x bits hp siteI codeFI ph ci LI layI
  (degOf sources selector coordI ph ci LI tgtI modeI layI) VI dfltI (InitRun.D0 bI) (InitRun.cap0 bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI)
  (CloseoutFinalC10AppendWorkspaceInit.capacity bI) oldI HdZI AdZI RcI costI costI costI RcI
set_option hygiene false in
local notation "capsI" => capsSite mask packets rows sources hg hh p kI n
set_option hygiene false in
local notation "layAI" => layoutAtOf sources selector coordI ph ci LI tgtI modeI layI
set_option hygiene false in
local notation "factsAI" => factsAtOf sources selector compiler coordI ph ci LI tgtI modeI
set_option hygiene false in
local notation "gWI" => (DSite selector mask packets rows sources gamma hg hh p).gW
set_option hygiene false in
local notation "NNI" => (vdI).entries.length

theorem hTNFS (semantics : PCJ9eff70d512234a4c_Fixed.Certificate) (compiler : Packets.CompilerLaws)
    (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) (ci : Fin NCI) (A : Fin BTSI → List Bool) (H : Fin BTSI → Nat)
    (Hv : Nat → Fin UI → Nat) (Av : Nat → Fin UI → List Bool) :
    TraceNums mask selector packets rows compiler sources p (denI) (Nat.succ_pos _) kI rI (scratchOf mask packets rows sources resI) n x bits hp siteI codeFI ph ci LI layI
      (degOf sources selector coordI ph ci LI tgtI modeI layI) VI dfltI (InitRun.D0 bI) (InitRun.cap0 bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI)
      (CloseoutFinalC10AppendWorkspaceInit.capacity bI) oldI HdZI AdZI RcI costI costI costI RcI H A SFI NNI { vdI with H := Hv, A := Av } := by
  have hext := hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp
  have hon := NearCubicWires.SourceFactorSel.OnsetFin.pastE_siteOnGF selector mask packets rows sources gamma hg hh p n hext
  unfold NearCubicWires.SourceFactorSel.SeamSiteGF.siteOnGF at hon
  simp only [max_le_iff] at hon
  obtain ⟨-, -, -, o4, -⟩ := hon
  have h201 := (NearCubicWires.SourceStart.LayRP.layOnW_spec selector mask packets rows sources gamma hg hh p n
    (NearCubicWires.SourceFactorSel.OnsetFin.pastE_layOnW selector mask packets rows sources gamma hg hh p n hext)).1
  exact NearCubicWires.SourceFactorSel.TraceSiteGF.traceNums_site mask selector packets rows compiler sources hg hh p
    (SourceBudget.capIndexOf (ParamsV4.den0W selector mask packets rows)) (denI) (Nat.succ_pos _) kI rI (scratchOf mask packets rows sources resI) n x bits hp siteI codeFI ph ci LI layI
    (degOf sources selector coordI ph ci LI tgtI modeI layI) VI dfltI oldI HdZI AdZI RcI costI costI costI RcI semantics Hv Av H A SFI NNI
    rfl rfl rfl (Nat.succ_pos _) o4 rfl rfl (fun _ => rfl) (fun _ => rfl) h201 rfl (List.length_take_le _ _) (fun j => if_neg (Nat.succ_ne_zero j))
    rfl rfl rfl rfl

theorem goodFS (compiler : Packets.CompilerLaws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) (ci : Fin NCI) (m : Nat) :
    RowCaps.Good selector (decompositionOf sources) (printerOf sources) (requestAt coordI ph ci LI tgtI modeI m) (layAI m) (factsAI m) capsI := by
  have hext := hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp
  have h201 := (NearCubicWires.SourceStart.LayRP.layOnW_spec selector mask packets rows sources gamma hg hh p n
    (NearCubicWires.SourceFactorSel.OnsetFin.pastE_layOnW selector mask packets rows sources gamma hg hh p n hext)).1
  obtain ⟨hsd, hso⟩ := NearCubicWires.SourceStart.YSite.small_adm selector mask packets rows sources gamma hg hh p 𝔛 n hext
  exact goodAt_site mask packets rows sources hg hh p kI rI (scratchOf mask packets rows sources resI) (denI) (Nat.succ_pos _) n x bits hp ph ci layAI factsAI
    (fun m => NearCubicWires.SourceStart.YSite.layoutAtOf_degree sources selector coordI ph ci LI tgtI modeI layI m)
    (fun m => NearCubicWires.SourceStart.YSite.layoutAtOf_C sources selector coordI ph ci LI tgtI modeI layI m)
    (hcutFS selector mask packets rows sources gamma hg hh p n x bits hn hp) h201 hsd hso m

theorem hSNFS (compiler : Packets.CompilerLaws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) (ci : Fin NCI) (A : Fin BTSI → List Bool) (g7c : Nat → Nat)
    (hG : ∀ j, g7c (j+1) ≤ RuntimeShape.tableClass LI 0 (C10PartsSchedule.widthAt sources kI n)) :
    SeamNums mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI g7c preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI ci LI RcI (InitS.Rk RcI) bI layI
      (fun _ => capsI) (goodFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci) KI K0I KH0I VI dfltI
      (InitRun.D0 bI) (InitRun.cap0 bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI) HdZI AdZI oldI
      costI costI RcI RcI RcI RcI RcI costI NNI := by
  have hext := hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp
  have hon := NearCubicWires.SourceFactorSel.OnsetFin.pastE_siteOnGF selector mask packets rows sources gamma hg hh p n hext
  have hcut := hcutFS selector mask packets rows sources gamma hg hh p n x bits hn hp
  have h201 := (NearCubicWires.SourceStart.LayRP.layOnW_spec selector mask packets rows sources gamma hg hh p n
    (NearCubicWires.SourceFactorSel.OnsetFin.pastE_layOnW selector mask packets rows sources gamma hg hh p n hext)).1
  obtain ⟨hsd, hso⟩ := NearCubicWires.SourceStart.YSite.small_adm selector mask packets rows sources gamma hg hh p 𝔛 n hext
  have o4 : (SourceSteps.selR sources p kI).onset ≤ n := by
    have h := hon
    unfold NearCubicWires.SourceFactorSel.SeamSiteGF.siteOnGF at h
    simp only [max_le_iff] at h
    exact h.2.2.2.1
  have hNb : NNI ≤ bI :=
    NearCubicWires.SourceStart.SeamRP.phaseE_len_le_b sources p (denI) kI (SourceSteps.selR sources p kI) o4 x bits modeI ph LI ci
  have KN := NearCubicWires.SourceRequest.SelKeptNums.seamNumsKept selector 𝔛 mask packets rows sources gamma hg hh p hresI ph eI g7FI g7c preFFI compiler
    (denI) (Nat.succ_pos _) n x bits hp siteI ci LI RcI (InitS.Rk RcI) bI layI (fun _ => capsI) (goodFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci)
    VI dfltI (InitRun.D0 bI) (InitRun.cap0 bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI) HdZI AdZI oldI
    costI costI RcI RcI RcI RcI RcI costI NNI modeI (RepairOrdinary.frame bits) (ZeroPadding.pad capCI (SourceSteps.qwordAt sources p kI n x bits ci.val))
    (Function.update (SourceSteps.cdAt sources p kI n x bits ci.val) 15 (List.replicate capCI false))
    (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeI n bI) VI NCI
    (fun i => NearCubicWires.SourceRequest.SelStripLen.resWSite_len selector mask packets rows sources gamma hg hh p modeI n bI i) (fun _ => rfl)
  have hY := NearCubicWires.SourceStart.YSite.y1_site mask packets rows sources resI p kI rI hg hh compiler (denI) (Nat.succ_pos _) n x bits hp ph ci LI layI
    (fun _ => capsI) VI bI NNI rfl rfl rfl rfl (fun _ => rfl) (fun _ => NearCubicWires.SourceStart.MetaRun.wA_le _ _) (fun _ => rfl) (fun _ => rfl)
    hcut h201 hsd hso hNb
  exact NearCubicWires.SourceFactorSel.SeamSiteGF.seamNums_site mask packets rows sources resI hresI p kI rI hg hh ph seI spI eI g7FI g7c preFFI compiler
    (denI) (Nat.succ_pos _) n x bits hp siteI ci LI RcI (InitS.Rk RcI) bI layI (fun _ => capsI) (goodFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci)
    KI K0I KH0I VI dfltI (InitRun.D0 bI) (InitRun.cap0 bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI) HdZI AdZI oldI
    costI costI RcI RcI RcI RcI RcI costI NNI
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl rfl rfl (fun _ => rfl) hon hY (fun j _ => hG j)
    KN.hKpos KN.hKpad KN.hKapp KN.hKfree KN.hKr1 KN.hKr2

theorem hSeamFS (compiler : Packets.CompilerLaws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) (g7c : Fin NCI → Nat → Nat)
    (hG : ∀ (ci : Fin NCI) j, g7c ci (j+1) ≤ RuntimeShape.tableClass LI 0 (C10PartsSchedule.widthAt sources kI n))
    (hG7 : ∀ ci : Fin NCI, ResidentRunH (g7FI ph).2 (g7c ci) mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇I).maskSlots 𝒽I) ((𝔇I).pslots 𝒽I) ((𝔇I).slot 𝒽I) ((𝔇I).ret 𝒽I) ((𝔇I).scr 𝒽I 0) ((𝔇I).scr 𝒽I 1)
      ((𝔇I).familySlots 𝒽I) ((𝔇I).poolSlots 𝒽I) (Dims.rewind2Slots (eI).ext2.ext1.ext 𝒽I)
      ((𝔇I).scr 𝒽I 5) ((𝔇I).scr 𝒽I 6) ((𝔇I).scr 𝒽I 7) ((𝔇I).scr 𝒽I 8) ((𝔇I).scr 𝒽I 9) ((𝔇I).scr 𝒽I 10)
      (Dims.lenTape (eI).ext2.ext1.ext 𝒽I) coordI ph ci LI tgtI modeI RcI bI
      ((𝔇I).pcT (eI).ext2.ext1 𝒽I ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇I).pcT (eI).ext2.ext1 𝒽I ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layAI (fun _ => capsI)
      (Dims.Rpad (d := 𝔇I) (eX := (seI).extra) (pX := (spI).extra) (gW := gWI) (V := UI) RcI)
      (RestIn4 (𝔇I) (seI).extra (spI).extra gWI RcI ((𝔇I).pcT (eI).ext2.ext1 𝒽I ⟨64, by unfold restPc; omega⟩) KI K0I KH0I)
      (fun z => OutV (𝔇I) (seI).extra (spI).extra gWI z.val)) :
    ∀ (ci : Fin NCI) (A : Fin BTSI → List Bool) (H1 : Fin (UI + 1) → Nat) (A1 : Fin (UI + 1) → List Bool),
      SeamSpec NNI (fun _ => 0) (𝒞I).slots (inTOf 𝒞I bI vdI) (InvXFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci A H1 A1)
        (goodOf 𝒞I bI vdI) := by
  intro ci A H1 A1
  have SN := hSNFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci A (g7c ci) (hG ci)
  exact seam6_clause mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI (g7c ci) preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI ci LI RcI
    (InitS.Rk RcI) bI layI (fun _ => capsI) (goodFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci) KI K0I KH0I (hG7 ci) VI dfltI
    (InitRun.D0 bI) (InitRun.cap0 bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI) HdZI AdZI oldI
    (fun j => if_neg (Nat.succ_ne_zero j)) costI costI RcI RcI RcI RcI RcI costI NNI
    SN.hlay SN.hL1 SN.hu SN.hRk SN.hcW SN.hcQ SN.hcB SN.hcS SN.hSl SN.hRl SN.hBl SN.h4b SN.hUl SN.hMb SN.hMs SN.hKpos SN.hKpad SN.hKapp SN.hKfree SN.hKr1 SN.hKr2
    SN.hj SN.hRc SN.hlog SN.he1 SN.hpw SN.hfirst SN.hsecond SN.hdescR SN.hL SN.hfamH SN.hwinI SN.hwinZ SN.hcost
    (fun y => H1 y.castSucc) (chainView 𝒞I bI vdI NNI 0 (fun y => A1 y.castSucc))

end fields

end
end NearCubicWires.SourceSkeleton.Final
end

