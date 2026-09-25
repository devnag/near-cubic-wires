import Proof.SourceAssembly.SourceStepsSite2
import Proof.Packets.SrcStartStatic

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
namespace NearCubicWires.SourceStart.C2RP
open NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section rprows
open Classical
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)
  (ph : Phase)
  (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
  (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
  (e : (dimsOf mask packets rows sources res p k r).RestExt3 se.extra sp.extra gW)
  (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s)
  (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
  (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
  (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
  (L Rc Rk : Nat)
  (layF : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)),
    TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp) selector)
  (K : Fin (UOf mask packets rows sources res p k r) → Prop)
  (K0F : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → Fin (UOf mask packets rows sources res p k r) → List Bool)
  (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
  (V : Nat) (dflt : P1TopDownPaidReusable.Datum)
  (familyCost firstCost counterReserve refillCost : Nat)

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
local notation "bS" => C10PartsSchedule.entryWidthSchedule sources k r n
set_option hygiene false in
local notation "BTS" => ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)
set_option hygiene false in
local notation "CACHES" => PCJda54a286946142d3_BranchPhases.cache sources p k r (scratchOf mask packets rows sources res) modeC
set_option hygiene false in
local notation "layC" => layF ci
set_option hygiene false in
local notation "K0C" => K0F ci
set_option hygiene false in
local notation "HdZ" => (fun (_ : Nat) (_ : Fin (UOf mask packets rows sources res p k r)) => (0 : Nat))
set_option hygiene false in
local notation "AdZ" => (fun (_ : Nat) (_ : Fin (UOf mask packets rows sources res p k r)) => ([] : List Bool))
set_option hygiene false in
local notation "w0C" => (A ((𝒞).whole (Dims.encT (d := 𝔇) 𝒽 5).castSucc)).take (InitRun.D0 bS)
set_option hygiene false in
local notation "oldC" => fun j => if j = 0 then w0C else oldAt coordC ph ci sources L tgtC modeC bS (InitRun.D0 bS) j
set_option hygiene false in
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L layC (degOf sources selector coordC ph ci L tgtC modeC layC) V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) oldC HdZ AdZ Rc familyCost refillCost firstCost counterReserve
set_option hygiene false in
local notation "NC5" => (vdC).entries.length
set_option hygiene false in
local notation "CSPC" => (ChainStartP mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS layC K K0C KH0 V dflt HdZ AdZ familyCost firstCost counterReserve refillCost Rc Rc Rc Rc w0C A H)
set_option hygiene false in
local notation "Inv5C" => (Inv5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS layC K K0C KH0 V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) HdZ AdZ oldC familyCost firstCost counterReserve refillCost Rc Rc Rc Rc NC5)
set_option hygiene false in
local notation "startC" => (if hst : ∃ H1 A1, SP ci A H H1 A1 then (Classical.choose hst, Classical.choose (Classical.choose_spec hst)) else ((fun _ => 0 : Fin (UOf mask packets rows sources res p k r + 1) → Nat), (fun _ => [] : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)))
set_option hygiene false in
local notation "H0C" => (fun y : Fin (UOf mask packets rows sources res p k r) => (startC).1 y.castSucc)
set_option hygiene false in
local notation "A0C" => chainView 𝒞 bS vdC NC5 0 (fun y : Fin (UOf mask packets rows sources res p k r) => (startC).2 y.castSucc)
set_option hygiene false in
local notation "seamC" => hSeam ci A (startC).1 (startC).2
set_option hygiene false in
local notation "VVC" => chainVals 𝒞 bS vdC seamC H0C A0C
set_option hygiene false in
local notation "ES" => (⟨𝔇, se.extra, sp.extra, gW, eR, eV, X, (𝒞).sourceTapes + 1, (𝒞).whole, pl, e, Rc, Rk, Ce, Kc, K0e, KH0e, cnt, c15, q284, c17, c18,
  bS, vQ, vMB, vMS, vWS, vRW, vBF, vU0⟩ : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)))
set_option hygiene false in
local notation "NCC" => NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)
set_option hygiene false in
local notation "UU" => UOf mask packets rows sources res p k r

structure RPRows (Et : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)))
    {eR : Nat} {eV : Nat} {X : Nat} (pl : Phase → InitRun.Place 𝔇 se.extra sp.extra gW eR eV X ((𝒞).sourceTapes + 1)) (Ce : Nat) (Kc : Fin ((𝒞).sourceTapes + 1) → Prop) (K0e : Phase → Nat → Fin ((𝒞).sourceTapes + 1) → List Bool) (KH0e : Fin ((𝒞).sourceTapes + 1) → Nat) (cnt : Fin ((𝒞).sourceTapes + 1)) (c15 : Fin ((𝒞).sourceTapes + 1)) (q284 : Fin ((𝒞).sourceTapes + 1)) (c17 : Fin ((𝒞).sourceTapes + 1)) (c18 : Fin ((𝒞).sourceTapes + 1)) : Prop where
  hNR : ∀ (ci : Fin NCC) (A : Fin BTS → List Bool), NC5 + 2 ≤ Rc
  hwR : ∀ (ci : Fin NCC) (A : Fin BTS → List Bool), (CompareMachine.word NC5).length ≤ Rc
  hcnt : cnt = Fin.last (𝒞).sourceTapes
  hcacheK : ∀ (ci : Fin NCC) (i : Fin 19) (s : Fin (𝒞).sourceTapes), (𝒞).whole s.castSucc = CACHES i →
      K s ∧ K0C s = CD sources k (PolynomialClock.ordinaryClock k) x oracleC ci.val i ∧ KH0 s = 0
  hKc1 : ∀ (ci : Fin NCC) (y : Fin (𝒞).sourceTapes), Kc y.castSucc → K y ∧ KH0e y.castSucc = KH0 y ∧
      ((∀ i, (𝒞).whole y.castSucc ≠ CACHES i) → K0e ph (ci.val+1) y.castSucc = K0C y)
  hKc2 : ∀ (ci : Fin NCC) y (i : Fin 19), Kc y → (𝒞).whole y = CACHES i → K0e ph (ci.val+1) y = cdAt sources p k n x bits (ci.val+1) i ∧ KH0e y = 0
  hKlast : ¬ Kc (Fin.last (𝒞).sourceTapes)
  h15 : (𝒞).whole c15 = CACHES 15
  h17 : (𝒞).whole c17 = CACHES 17
  h18 : (𝒞).whole c18 = CACHES 18
  hq284F : q284.val < (𝔇).F
  hq284c : ∀ i, (𝒞).whole q284 ≠ CACHES i
  hq284 : ∀ ci : Fin NCC, ∃ y : Fin (𝒞).sourceTapes, y.castSucc = q284 ∧ K y ∧ (K0C y).length ≤ capC sources k (PolynomialClock.ordinaryClock k) x oracleC ∧ KH0 y = 0
  hEt : Et = ES

end rprows

/-- An entry site equals itself with its init constants `Mb Ms U0` restated (the one non-definitional part of `hEt`). -/
theorem entrySite_upd {BT : ℕ} (E : SourceSteps.EntrySite BT) (a b c : ℕ) (ha : E.Mb = a) (hb : E.Ms = b) (hc : E.U0 = c) :
    E = { E with Mb := a, Ms := b, U0 := c } := by
  subst ha hb hc
  rfl

/-- `clauseData` reads the query word only at index `15`. -/
theorem clauseData_off15 (src : List Bool) (ar idx C : ℕ) (w w' : List Bool) (i : Fin 19) (h : i ≠ 15) :
    PCPPQueryIndexPadding.clauseData src ar idx C w i = PCPPQueryIndexPadding.clauseData src ar idx C w' i := by
  fin_cases i <;> simp [PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data] at h ⊢

/-- Blanking the query word: `Function.update (clauseData … w) 15 0^C = clauseData … []`. -/
theorem update_clauseData (src : List Bool) (ar idx C : ℕ) (w : List Bool) :
    Function.update (PCPPQueryIndexPadding.clauseData src ar idx C w) 15 (List.replicate C false) =
      PCPPQueryIndexPadding.clauseData src ar idx C [] := by
  funext i
  by_cases h : i = 15
  · subst h
    rw [Function.update_self]
    simp [PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data, ZeroPadding.pad]
  · rw [Function.update_of_ne h]
    exact clauseData_off15 src ar idx C w [] i h

/-- **The cache contents with the query word blank**: `Function.update (cdAt ci) 15 0^capC = CD ci` (`clauseData` reads the query word
only at index `15`, where `pad C [] = 0^C`). -/
theorem cd_update (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k n : ℕ) (x : BitInput n) (bits : List Bool) (ci : ℕ) :
    Function.update (SourceSteps.cdAt sources p k n x bits ci) 15
        (List.replicate (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) false) =
      CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ci :=
  update_clauseData _ _ _ _ _

section rpsite
open NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.KeptW NearCubicWires.SourceSkeleton.ClassV4 NearCubicWires.SourceSkeleton.ParamsV4
variable (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector)
  (G7 : FirstW.G7W selector xtra)

set_option hygiene false in
local notation "CODE" => skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows)
  (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows))
  (ParamsV4.fPW selector xtra mask packets rows)
  (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _
    (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)
set_option hygiene false in
local notation "𝔉" => forcedChoices mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows)
set_option hygiene false in
local notation "denI" => (𝔉).capIndex sources gamma hg hh p + 1
set_option hygiene false in
local notation "kI" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "rI" => rSite selector xtra mask packets rows sources gamma hg hh p
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
local notation "eI" => eSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "hresI" => resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows) sources gamma hg hh p
set_option hygiene false in
local notation "g7FI" => fun ph' => FirstW.g7OfW selector xtra G7 mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "preFFI" => fun ph' => FirstW.firstW selector xtra G7 mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "siteI" => (CODE).site sources gamma hg hh p
set_option hygiene false in
local notation "EtI" => EWFam selector xtra mask packets rows (CODE) sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "EFI" => EFSite selector xtra G7 mask packets rows sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "SFI" => ParamsV4.sfPW selector mask packets rows sources gamma hg hh p n x bits ph
set_option hygiene false in
local notation "KI" => KeptW.KSite selector xtra mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI
set_option hygiene false in
local notation "KH0I" => (fun (_ : Fin UI) => (0 : Nat))
set_option hygiene false in
local notation "𝒞I" => skelCodeR mask packets rows sources resI hresI p kI rI ph (refill3 mask packets rows sources resI p kI rI seI spI eI (g7FI ph).2) (preFFI ph)

set_option hygiene false in
local notation "𝔨" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔘" => USite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯𝔢𝔰" => resSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔙" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔒" => C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits
set_option hygiene false in
local notation "ℭℭ" => PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "𝔠𝔞𝔭" => capC sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) x
  (C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
    (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits)

def K0FW (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) (ci : ℕ) :
    Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → List Bool :=
  K0Site selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) mode
    (RepairOrdinary.frame bits) (ZeroPadding.pad 𝔠𝔞𝔭 (SourceSteps.qwordAt sources p 𝔨 n x bits ci))
    (Function.update (SourceSteps.cdAt sources p 𝔨 n x bits ci) 15 (List.replicate 𝔠𝔞𝔭 false))
    (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n (C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n)) 𝔙
    (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒)

theorem KSite_of_castSucc (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (V : ℕ) (hV : (𝔡).U ≤ V) (hV1 : (𝔡).U ≤ V + 1) (mode : Bool) (y : Fin V)
    (hy : KSite selector xtra mask packets rows sources gamma hg hh p (V + 1) hV1 mode y.castSucc) :
    KSite selector xtra mask packets rows sources gamma hg hh p V hV mode y := by
  rcases hy with h | h | h | h | h | h
  · left
    rcases h with h | h | ⟨i, hi⟩ | h
    · left; simpa using h
    · right; left; simpa using h
    · right; right; left
      refine ⟨i, Fin.ext ?_⟩
      have hv := congrArg Fin.val hi
      rw [cacheSite_val, Fin.val_castSucc] at hv
      rw [cacheSite_val]
      exact hv
    · right; right; right; simpa using h
  · right; left; simpa using h
  · right; right; left; simpa using h
  · right; right; right; left; simpa using h
  · right; right; right; right; left; simpa using h
  · right; right; right; right; right
    refine Fin.ext ?_
    have hv := congrArg Fin.val h
    rw [Fin.val_castSucc] at hv
    rw [hv]
    rfl

/-- A non-cache kept word off `284` along `castSucc` (any query copy and cache words on either side: they are read only at `284` and the cache). -/
theorem K0Site_castSucc_off (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (V : ℕ) (hV : (𝔡).U ≤ V) (hV1 : (𝔡).U ≤ V + 1) (mode : Bool) (frameW qW qW' : List Bool) (cdW cdW' : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) (y : Fin V) (hc : ∀ i, (ℭℭ mode i).val ≠ y.val) (h284 : y.val ≠ 284) :
    K0Site selector xtra mask packets rows sources gamma hg hh p (V + 1) hV1 mode frameW qW cdW resW Vv NC y.castSucc =
      K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW' cdW' resW Vv NC y := by
  have hc1 : ∀ i, (ℭℭ mode i).val ≠ y.castSucc.val := fun i h => hc i (by rw [Fin.val_castSucc] at h; exact h)
  rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p (V + 1) hV1 mode _ _ _ _ _ _ y.castSucc hc1,
    K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode _ _ _ _ _ _ y hc]
  simp only [Fin.val_castSucc]
  by_cases ht : y = terminalSite selector xtra mask packets rows sources gamma hg hh p V hV
  · have ht1 : y.castSucc = terminalSite selector xtra mask packets rows sources gamma hg hh p (V + 1) hV1 :=
      Fin.ext (by rw [Fin.val_castSucc, ht]; rfl)
    simp only [eq_true ht1, eq_true ht, eq_false h284, ↓reduceIte]
  · have ht1 : ¬ y.castSucc = terminalSite selector xtra mask packets rows sources gamma hg hh p (V + 1) hV1 := fun h =>
      ht (Fin.ext (by
        have hv := congrArg Fin.val h
        rw [Fin.val_castSucc] at hv
        rw [hv]
        rfl))
    simp only [eq_false ht1, eq_false ht, eq_false h284, ↓reduceIte]

theorem rpRows_site (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase)
    (layF : ∀ ci : Fin NCI, TraceData.LayoutFamily coordI ph ci sources LI tgtI modeI selector)
    (dflt : P1TopDownPaidReusable.Datum) (familyCost firstCost refillCost : Nat)
    (hext : ParamsV4.extraW selector xtra mask packets rows sources gamma hg hh p ≤ n)
    (hsOn : NearCubicWires.SourceStart.SeamRP.seamOnW selector mask packets rows sources gamma hg hh p ≤ n) :
    RPRows mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI LI RcI (InitS.Rk RcI)
      layF KI (fun ci => K0FW selector xtra mask packets rows sources gamma hg hh p modeI n x bits ci.val) KH0I VI dflt familyCost firstCost RcI refillCost
      EtI (EtI).pl (EtI).Ce (EtI).Kc (EtI).K0 (EtI).KH0 (EtI).cnt (EtI).c15 (EtI).q284 (EtI).c17 (EtI).c18 := by
  have hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n :=
    (NearCubicWires.SourceStart.LayRP.layF_adm selector mask packets rows sources gamma hg hh p xtra n hext).1
  have hvq : (req sources kI (PolynomialClock.ordinaryClock kI) x oracleI).arity =
      C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n :=
    Admission.req_arity sources kI (PolynomialClock.ordinaryClock kI) x _ hcut
  have hs := NearCubicWires.SourceStart.SeamRP.seamOn_site selector mask packets rows sources gamma hg hh p xtra n hsOn
  unfold NearCubicWires.SourceStart.SeamRP.seamOn at hs
  simp only [max_le_iff] at hs
  obtain ⟨-, -, n3, n4⟩ := hs
  have hq0 := Classical.choose_spec (SourceBudget.widthAt_ge_eventually sources kI
    (Classical.choose (SourceSteps.enc_sat_at sources kI (SourceSteps.rBsel sources p) (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)))) n n3
  have h4b : 4 * bI + 5 ≤ RcI := Classical.choose_spec (SourceSteps.enc_sat_at sources kI (SourceSteps.rBsel sources p)
    (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)) n hq0 1 (hRx4 selector mask packets rows sources gamma hg hh p) le_rfl
  have key : ∀ ci : Fin NCI, (SourceSkeleton.phaseE sources p (denI) kI x bits modeI ph LI ci).length + 2 ≤ RcI := fun ci => by
    have hNb : (SourceSkeleton.phaseE sources p (denI) kI x bits modeI ph LI ci).length ≤ bI :=
      NearCubicWires.SourceStart.SeamRP.phaseE_len_le_b sources p (denI) kI (SourceSteps.selR sources p kI) n4 x bits modeI ph LI ci
    omega
  refine
    { hNR := fun ci _ => ?_
      hwR := fun ci _ => ?_
      hcnt := ?_
      hcacheK := fun ci i s hs => ?_
      hKc1 := fun ci y hy => ?_
      hKc2 := fun ci y i hy hw => ?_
      hKlast := fun h => ?_
      h15 := ?_
      h17 := ?_
      h18 := ?_
      hq284F := ?_
      hq284c := fun i h => ?_
      hq284 := fun ci => ?_
      hEt := ?_ }
  · -- hNR
    show (SourceSkeleton.phaseE sources p (denI) kI x bits modeI ph LI ci).length + 2 ≤ RcI
    exact key ci
  · -- hwR
    have k := key ci
    show (RepairSource.VerifierDecoding.CompareMachine.word (SourceSkeleton.phaseE sources p (denI) kI x bits modeI ph LI ci).length).length ≤ RcI
    simp only [RepairSource.VerifierDecoding.CompareMachine.word, List.length_cons, List.length_replicate]
    omega
  · -- hcnt
    rfl
  · -- hcacheK
    have e1 : s.castSucc.val = (PCJda54a286946142d3_BranchPhases.cache sources p kI rI (scratchOf mask packets rows sources resI) modeI i).val := ((𝒞I)._hwhole s.castSucc).symm.trans (congrArg Fin.val hs)
    have hsv : s = cacheSite selector xtra mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI i :=
      Fin.ext (((Fin.val_castSucc s).symm.trans e1).trans
        (cacheSite_val selector xtra mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI i).symm)
    subst hsv
    refine ⟨?_, ?_, rfl⟩
    · left; right; right; left; exact ⟨i, rfl⟩
    · show K0FW selector xtra mask packets rows sources gamma hg hh p modeI n x bits ci.val _ = _
      unfold K0FW
      rw [K0Site_cache, cd_update]
  · -- hKc1
    change KcW selector xtra mask packets rows sources gamma hg hh p modeI y.castSucc at hy
    obtain ⟨hk, -, hq⟩ := hy
    refine ⟨KSite_of_castSucc selector xtra mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) (Nat.le_succ _) modeI y hk,
      rfl, fun hc => ?_⟩
    have h284 : y.val ≠ 284 := fun h => hq (Fin.ext (by rw [Fin.val_castSucc, h]; rfl))
    have hc0 : ∀ i, (ℭℭ modeI i).val ≠ y.val := fun i h =>
      hc i (Fin.ext (((𝒞I)._hwhole _).trans ((Fin.val_castSucc y).trans h.symm)))
    refine (ew_K0_eq selector xtra mask packets rows sources gamma hg hh p modeI n x bits ph (ci.val + 1) y.castSucc).trans ?_
    exact K0Site_castSucc_off selector xtra mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) (Nat.le_succ _) modeI
      _ _ _ _ _ _ _ _ y hc0 h284
  · -- hKc2
    refine ⟨ew_K0c selector xtra mask packets rows sources gamma hg hh p modeI n x bits ph (ci.val + 1) y i hy
      (Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p modeI n x bits y).trans
        (((𝒞I)._hwhole y).symm.trans (congrArg Fin.val hw)))), rfl⟩
  · -- hKlast
    change KcW selector xtra mask packets rows sources gamma hg hh p modeI _ at h
    have h1 := KSite_lt_U selector xtra mask packets rows sources gamma hg hh p _ _ modeI _ h.1
    have h3 : UI < (𝔡).U := h1
    have h2 : (𝔡).U ≤ UI := UOf_le mask packets rows sources resI p kI rI
    omega
  · -- h15
    exact Fin.ext (((𝒞I)._hwhole _).trans
      (cacheSite_val selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeI 15))
  · -- h17
    exact Fin.ext (((𝒞I)._hwhole _).trans
      (cacheSite_val selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeI 17))
  · -- h18
    exact Fin.ext (((𝒞I)._hwhole _).trans
      (cacheSite_val selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeI 18))
  · -- hq284F
    obtain ⟨hF, ho, -, -, -, -⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
    show 284 < (𝔡).F
    omega
  · -- hq284c
    have hv : 284 = (ℭℭ modeI i).val := ((𝒞I)._hwhole _).symm.trans (congrArg Fin.val h)
    have := cache_nums selector xtra mask packets rows sources gamma hg hh p modeI i
    omega
  · -- hq284
    refine ⟨q284Site selector xtra mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI), Fin.ext rfl, ?_, ?_, rfl⟩
    · left; right; left; rfl
    · show (K0FW selector xtra mask packets rows sources gamma hg hh p modeI n x bits ci.val _).length ≤ _
      unfold K0FW
      rw [K0Site_284, ZeroPadding.pad_length]
      exact max_le le_rfl (NearCubicWires.SourceStart.StartRP.qword_le_capC sources p kI n x bits ci)
  · -- hEt
    refine (entrySite_upd (EtI) (NearCubicWires.SourceConstruction.InitRun.Mb LI (req sources kI (PolynomialClock.ordinaryClock kI) x oracleI).arity)
      (NearCubicWires.SourceConstruction.InitPost.Ms LI (req sources kI (PolynomialClock.ordinaryClock kI) x oracleI).arity)
      (NearCubicWires.SourceConstruction.InitRun.U0 LI (req sources kI (PolynomialClock.ordinaryClock kI) x oracleI).arity) ?_ ?_ ?_).trans rfl
    · show NearCubicWires.SourceConstruction.InitRun.Mb LI (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n) = _
      rw [hvq]
    · show NearCubicWires.SourceConstruction.InitPost.Ms LI (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n) = _
      rw [hvq]
    · show NearCubicWires.SourceConstruction.InitRun.U0 LI (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n) = _
      rw [hvq]

end rpsite

end
end NearCubicWires.SourceStart.C2RP
end

