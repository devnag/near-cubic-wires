import Proof.Packets.SrcC2RP
import Proof.Packets.SrcCacheHole
import Proof.SourceAssembly.SourceSkelStartFS
import Proof.SourceAssembly.SourceStepsC2v5Holes
import Proof.SourceAssembly.SourceStepsC2v5Mk

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

set_option hygiene false in
local notation "SPI" => (fun (ci : Fin NCI) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p kI rI (scratchOf mask packets rows sources resI)) → List Bool)
  (H : Fin (ControllerSelectedContinuation.bodyTapes sources p kI rI (scratchOf mask packets rows sources resI)) → Nat) (H1 : Fin (UI + 1) → Nat) (A1 : Fin (UI + 1) → List Bool) =>
  ChainStartP5 mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI ci LI RcI
    (InitS.Rk RcI) bI (layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci) KI (K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci) KH0I VI
    (dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
    (fun (_ : Nat) (_ : Fin UI) => (0 : Nat)) (fun (_ : Nat) (_ : Fin UI) => ([] : List Bool))
    (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI
    (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI RcI RcI RcI
    ((A ((𝒞I).whole (Dims.encT (d := dimsOf mask packets rows sources resI p kI rI) (UOf_le mask packets rows sources resI p kI rI) 5).castSucc)).take (InitRun.D0 bI))
    A H H1 A1)

set_option hygiene false in
local notation "𝔮𝔰I" => C10PartsSchedule.widthAt sources kI n
set_option hygiene false in
local notation "MBCI" => NearCubicWires.SourceStart.MetaRun.MBof selector sources p packets LI 𝔮𝔰I
set_option hygiene false in
local notation "LdCqI" => SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) 𝔮𝔰I
set_option hygiene false in
local notation "cwidCI" => NearCubicWires.SourceSkeleton.InitS.cwidOf modeI LdCqI
set_option hygiene false in
local notation "cwCqI" => NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p * (𝔮𝔰I + 1) ^ NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p
set_option hygiene false in
local notation "DCqI" => NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p * (𝔮𝔰I + 1) ^ NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p
set_option hygiene false in
local notation "PwCI" => NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (𝔮𝔰I + 1) ^ NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p
set_option hygiene false in
local notation "WCqI" => SourceBudget.wCap 𝔮𝔰I
set_option hygiene false in
local notation "g7cI" => fun (ci : Fin NCI) => NearCubicWires.SourceRequest.SelG7Spec.g7costW sources mask MBCI (RepairSource.CloseoutLanguage.selectedPCPP sources)
  (req sources kI (PolynomialClock.ordinaryClock kI) x oracleI) ci coordI bits ph LI tgtI cwidCI cwCqI DCqI bI PwCI WCqI LdCqI modeI

theorem hGFS (compiler : Packets.CompilerLaws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) (ci : Fin NCI) (j : Nat) :
    (g7cI) ci (j+1) ≤ RuntimeShape.tableClass LI 0 𝔮𝔰I := by
  have hext := hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp
  have hcut := hcutFS selector mask packets rows sources gamma hg hh p n x bits hn hp
  obtain ⟨hadm, hq, hL⟩ := SourceSteps.site_call_facts sources p (denI) (Nat.succ_pos _) kI rI (scratchOf mask packets rows sources resI) n x bits hp ph ci LI
    (Nat.succ_pos _) hcut (j+1)
  exact NearCubicWires.SourceRequest.SelG7Final.g7cost_final selector 𝔛 mask packets rows sources gamma hg hh p LI tgtI (SourceBudget.tgt sources p) (denI) n
    (NearCubicWires.SourceFactorSel.OnsetFin.pastE_g7OnsetF selector mask packets rows sources gamma hg hh p n hext) x bits
    (NearCubicWires.SourceRequest.AdmitRead.hlen_site sources p (denI) (Nat.succ_pos _) kI x bits hp) modeI ph ci (Nat.succ_pos _) (j+1) hadm hq hL

theorem hSeamSite (compiler : Packets.CompilerLaws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) :
    ∀ (ci : Fin NCI) (A : Fin BTSI → List Bool) (H1 : Fin (UI + 1) → Nat) (A1 : Fin (UI + 1) → List Bool),
      SeamSpec NNI (fun _ => 0) (𝒞I).slots (inTOf 𝒞I bI vdI) (InvXFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci A H1 A1)
        (goodOf 𝒞I bI vdI) :=
  hSeamFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph (g7cI)
    (fun ci j => hGFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci j)
    (fun ci => NearCubicWires.SourceRequest.SelHG7Final.hG7_seam selector 𝔛 mask packets rows sources gamma hg hh p (denI) (Nat.succ_pos _) n x bits hp
      (hcutFS selector mask packets rows sources gamma hg hh p n x bits hn hp)
      (NearCubicWires.SourceFactorSel.OnsetFin.pastE_g7OnsetF selector mask packets rows sources gamma hg hh p n
        (hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp)) ph ci layI (fun _ => capsI)
      (fun m => NearCubicWires.SourceStart.YSite.layF_hMB selector packets sources p (denI) (Nat.succ_pos _) kI rI (scratchOf mask packets rows sources resI) n x bits hp ph ci LI
        (SourceBudget.Params.COf selector sources p (C10PartsSchedule.widthAt sources kI n)) p.clauseDegree (denI)
        (hden0FS selector mask packets rows sources gamma hg hh p n x bits hn hp) (hq0FS selector mask packets rows sources gamma hg hh p n x bits hn hp)
        (hAFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci) (h201FS selector mask packets rows sources gamma hg hh p n x bits hn hp)
        (fun _ => capsI) (fun _ => rfl) rfl (hcutFS selector mask packets rows sources gamma hg hh p n x bits hn hp) m)
      (fun _ => rfl))

theorem HsFS (semantics : PCJ9eff70d512234a4c_Fixed.Certificate) (compiler : Packets.CompilerLaws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) :
    C2Hyps5 mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI LI RcI (InitS.Rk RcI)
        (layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KI (K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KH0I VI
        (dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
        (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
        EtI EFI SFI (EtI).pl (EtI).Ce (EtI).Kc (EtI).K0 (EtI).KH0 (EtI).cnt (EtI).c15 (EtI).q284 (EtI).c17 (EtI).c18 SPI
        (InvXFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph) := by
  have hext := hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp
  have rp := NearCubicWires.SourceStart.C2RP.rpRows_site selector compiler 𝔛 (NearCubicWires.SourceFactorSel.G7W.G7Site selector 𝔛) mask packets rows sources gamma hg hh p
    n x bits hp ph (layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
    (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
    (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) hext
    (NearCubicWires.SourceFactorSel.OnsetFin.pastE_seamOnW selector mask packets rows sources gamma hg hh p n hext)
  have hSeam := hSeamSite selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph
  exact c2Hyps5_mk mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI LI RcI (InitS.Rk RcI)
    (layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KI (K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KH0I VI
    (dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
    (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
    EtI EFI SFI (EtI).pl (EtI).Ce (EtI).Kc (EtI).K0 (EtI).KH0 (EtI).cnt (EtI).c15 (EtI).q284 (EtI).c17 (EtI).c18
    hSeam
    (hStartFS selector compiler mask packets rows sources gamma hg hh p n x bits hn hp ph)
    (fun ci A H => hTNFS selector semantics compiler mask packets rows sources gamma hg hh p n x bits hn hp ph ci A H _ _)
    rfl
    (hK_6 mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI LI RcI (InitS.Rk RcI)
      (layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KI (K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KH0I VI
      (dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
      (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) hSeam)
    (fun ci A H => NearCubicWires.SourceStart.Holes.cacheHole mask selector packets rows sources p (denI) (Nat.succ_pos _) kI rI (scratchOf mask packets rows sources resI) n x bits hp
      (fun ph' => skelCodeR mask packets rows sources resI hresI p kI rI ph' (refill3 mask packets rows sources resI p kI rI seI spI eI (g7FI ph').2) (preFFI ph')) ph ci _)
    (hH_6 mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI LI RcI (InitS.Rk RcI)
      (layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KI (K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KH0I VI
      (dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
      (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) hSeam)
    (hN_6 mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI LI RcI (InitS.Rk RcI)
      (layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KI (K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) KH0I VI
      (dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
      (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) hSeam
      (EtI).pl (EtI).Ce (EtI).Kc (EtI).K0 (EtI).KH0 (EtI).cnt (EtI).c15 (EtI).q284 (EtI).c17 (EtI).c18 EFI
      rp.hcacheK
      (fun ci y hy hF => NearCubicWires.SourceSkeleton.KeptW.K0Site_pad selector 𝔛 mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI
        (RepairOrdinary.frame bits) (ZeroPadding.pad capCI (SourceSteps.qwordAt sources p kI n x bits ci.val))
        (Function.update (SourceSteps.cdAt sources p kI n x bits ci.val) 15 (List.replicate capCI false))
        (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeI n bI) VI NCI RcI
        (fun i => NearCubicWires.SourceRequest.SelStripLen.resWSite_len selector mask packets rows sources gamma hg hh p modeI n bI i) y hy hF)
      (by unfold InitS.Rk; omega))
    rfl rp.hNR rp.hwR rp.hcnt rp.hcacheK rp.hKc1 rp.hKc2 rp.hKlast rp.h15 rp.h17 rp.h18 rp.hq284F rp.hq284c rp.hq284 (fun ci A => rfl) (fun ci A => rfl) rp.hEt

/-- **THE CLOSED FILL** (source-gen-holes node): `SourceGenHoles3 selector compiler` from the node's context certificate `semantics`. -/
theorem sourceFinalTop (compiler : Packets.CompilerLaws) (semantics : PCJ9eff70d512234a4c_Fixed.Certificate) : SourceGenHoles3 selector compiler :=
  sourceFinalTop_of2 selector compiler (HsFS selector semantics compiler)

end fields

end
end NearCubicWires.SourceSkeleton.Final
end

