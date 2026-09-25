import Proof.SourceAssembly.SourceSkelStartC5
import Proof.Packets.SrcK0W2

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
namespace NearCubicWires.SourceSkeleton.StartC5W
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

/-- `InvC` reads the kept words only on its kept set. -/
theorem invC_congrK0 {d : SourceConstruction.Dims} {eX pX gW : Nat} {e : d.RestExt3 eX pX gW} {V : Nat} {hV : d.U ≤ V}
    {Rc Rk : Nat} {Kc : Fin V → Prop} {K0 K0' : Fin V → List Bool} {KH0 : Fin V → Nat} {cnt : Fin V}
    {w q Mb Ms cW cQ cB cS S Rw B v U0 : Nat} {H : Fin V → Nat} {A : Fin V → List Bool}
    (h : Rest.InvC e hV Rc Rk Kc K0 KH0 cnt w q Mb Ms cW cQ cB cS S Rw B v U0 H A) (hK : ∀ y, Kc y → K0' y = K0 y) :
    Rest.InvC e hV Rc Rk Kc K0' KH0 cnt w q Mb Ms cW cQ cB cS S Rw B v U0 H A :=
  { h with kept := fun y hy => by rw [hK y hy]; exact h.kept y hy }

/-- **The guard and S's first seam at any clause entry of the site** (the first half of `startHole4_site`). -/
theorem firstExit5W_site (G7 : FirstW.G7W selector xtra) (hres : 19 ≤ 𝔯𝔢𝔰) (ph : Phase)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) s)
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p 𝔨 𝔯 𝔰) states)
    (ci : Fin (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC))
    (lay : TraceData.LayoutFamily coordC ph ci sources 𝔏 tgtC modeC selector)
    (K : Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Prop)
    (K0 : Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Nat)
    (dflt : P1TopDownPaidReusable.Datum)
    (Hd : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → List Bool)
    (familyCost firstCost counterReserve refillCost : Nat)
    (g7cost : ℕ → ℕ) (capsAt : ℕ → RowCaps)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordC ph ci 𝔏 tgtC modeC m) (layA m) (factsA m) (capsAt m))
    -- the onset and the site's scalar facts
    (hn : extraW selector xtra mask packets rows sources gamma hg hh p ≤ n)
    (hxtra : XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ xtra mask packets rows sources gamma hg hh p)
    (hV1 : 1 ≤ SourceBudget.Params.cVcN selector sources gamma hg hh p)
    (hA : vQ = 𝔮)
    (hqw : (SourceSteps.qwordAt sources p 𝔨 n x bits ci.val).length ≤ 𝔠𝔞𝔭)
    -- S's first-seam premises (static)
    (hG7 : ResidentRunH (G7 mask packets rows sources gamma hg hh p modeC ph (𝔘 + 1) (Nat.le_succ _)).2 g7cost mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots 𝒽1) ((𝔇).pslots 𝒽1) ((𝔇).slot 𝒽1) ((𝔇).ret 𝒽1) ((𝔇).scr 𝒽1 0) ((𝔇).scr 𝒽1 1)
      ((𝔇).familySlots 𝒽1) ((𝔇).poolSlots 𝒽1) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1)
      ((𝔇).scr 𝒽1 5) ((𝔇).scr 𝒽1 6) ((𝔇).scr 𝒽1 7) ((𝔇).scr 𝒽1 8) ((𝔇).scr 𝒽1 9) ((𝔇).scr 𝒽1 10)
      (Dims.lenTape (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1) coordC ph ci 𝔏 tgtC modeC ℜ 𝔟
      ((𝔇).pcT (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layA capsAt
      (Dims.Rpad (d := 𝔇) (eX := (DSite selector mask packets rows sources gamma hg hh p).se.extra) (pX := (DSite selector mask packets rows sources gamma hg hh p).sp.extra) (gW := (DSite selector mask packets rows sources gamma hg hh p).gW) (V := 𝔘 + 1) ℜ)
      (RestIn4 (𝔇) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ℜ ((𝔇).pcT (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨64, by unfold restPc; omega⟩) (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (fun _ => (0 : ℕ)))
      (fun y => OutV (𝔇) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW y.val))
    (hRk : ℜ ≤ (InitS.Rk ℜ))
    (hRc4 : 4 ≤ ℜ)
    (hSl : vWS + 2 ≤ ℜ)
    (hRl : vRW + 2 ≤ ℜ)
    (hBl : vBF + 2 ≤ ℜ)
    (hvl : 𝔟 + 2 ≤ ℜ)
    (hUl : vU0 ≤ ℜ)
    (hMb : vMB ≤ ℜ)
    (hMs : vMS ≤ ℜ)
    (hKpos : ∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ≤ y.val ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 10 ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 11))
    (hKcnt : ∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → y ≠ (Fin.last 𝔘))
    (hKfree : ∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → Cycle.Free ((𝔇).slot 𝒽1) ((𝔇).maskSlots 𝒽1) ((𝔇).pslots 𝒽1) ((𝔇).poolSlots 𝒽1)
      ((𝔇).familySlots 𝒽1) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1) y ∨
      y = Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1 ∨ y = Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2)
    (hKr1 : (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) →
      (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) = List.replicate (capsAt 0).descriptorReserve true ∧
      (fun _ => (0 : ℕ)) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) = 0)
    (hKr2 : (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) →
      (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) = List.replicate (capsAt 0).descriptorReserve false ∧
      (fun _ => (0 : ℕ)) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) = 0)
    (hK15 : (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (ℭ𝔖 modeC 15) → (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (ℭ𝔖 modeC 15) = List.replicate 𝔠𝔞𝔭 false ∧ (fun _ => (0 : ℕ)) (ℭ𝔖 modeC 15) = 0)
    (hK284 : (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) 𝔔 → (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) 𝔔 = 𝔴𝔮 ∧ (fun _ => (0 : ℕ)) 𝔔 = 0)
    (hN : (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordC ph ci).length).length ≤ ℜ)
    (hlog : 2 * ((requestAt coordC ph ci 𝔏 tgtC modeC 0).input (decompositionOf sources)).length + 1 ≤ ℜ)
    (he1 : 1 ≤ (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0))
    (hpw : (CloseoutRowsCountBinary.bits ((PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0))).length ≤ 𝔟)
    (hfirst : (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * 2^(natBitLength ((PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0))) < 2^𝔟)
    (hsecond : (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * 2^(vQ+1) < 2^𝔟)
    (hdescR : (capsAt 0).descriptorReserve ≤ ℜ)
    (hL : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length + 3 ≤ ℜ)
    (hfamH0 : ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC 0)) (layA 0) (factsA 0)) vWS vRW vBF (dataList (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC 0)) (layA 0) (factsA 0)).length i + (fuelOf 𝒞 𝔟 vdS0 0) + 1 ≤ ℜ)
    (hwinI0 : g7cost 0 + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) (layA 0) (factsA 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF 𝔟 (0)) + 1 ≤ ℜ)
    (hwinZ0 : (g7cost 0 + 1 + backCost (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (requestAt coordC ph ci 𝔏 tgtC modeC 0) ℜ 𝔟 vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length vMB vMS) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) (layA 0) (factsA 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF 𝔟 (0)) + 1 ≤ (InitS.Rk ℜ))
    (hcost0 : (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) (layA 0) (factsA 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF 𝔟 (𝔦𝔠 + 1 + ((4*(InitS.Rk ℜ)+7) + 1 + (((4*ℜ+7) + 1 + ((4*ℜ+7) + 1 + ((2*𝔠𝔞𝔭+4) + 1 + (2*𝔠𝔞𝔭+4) + 1 + (2*𝔠𝔞𝔭+4)))) + 1 + ((g7cost 0 + 1 + backCost (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (requestAt coordC ph ci 𝔏 tgtC modeC 0) ℜ 𝔟 vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length vMB vMS) + 1 + (refreshCost ℜ + 1 + ((2*ℜ+4) + 1 + 1))))))) ≤ firstCost)
    -- the call-0 row width (layout rows)
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg vQ 𝔏) (hL1 : 1 ≤ 𝔏)
    (hu : 1 ≤ vQ / (200 * (normalizedLiveCount vQ 𝔏 + 1 + 1)))
    -- the kept set on `U` (`first_startV`)
    (hKposU : ∀ y, K y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ≤ y.val ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽 10 ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽 11))
    (hK : ∀ y, K y → KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC y.castSucc)
    (hK0 : ∀ y, K y → K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val y.castSucc = K0 y ∧ (0 : ℕ) = KH0 y)
    (hKapp : ∀ y, K y → ∀ i, (𝒞).app i ≠ y)
    (hcR : counterReserve = ℜ)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p 𝔨 𝔯 𝔰) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p 𝔨 𝔯 𝔰) → ℕ)
    (hI : SourceSteps.entryInvAt4 sources p den hden 𝔨 𝔯 𝔰 n x bits hp (EW selector xtra mask packets rows sources gamma hg hh p modeC n x bits)
      (fun ph' => phaseE sources p den 𝔨 x bits modeC ph' 𝔏) ph ci.val A H) :
    ∃ (Hi H' : Fin (𝔘 + 1) → ℕ) (Ai A' : Fin (𝔘 + 1) → List Bool),
      (∀ y : Fin (𝔘 + 1), y.val < (𝔡).F → (y.val < 278 ∨ 284 ≤ y.val) →
        Ai y = SourceSteps.queriedAt sources p den hden 𝔨 𝔯 𝔰 n x bits hp ci.val A (wholeW selector xtra mask packets rows sources gamma hg hh p y) ∧ Hi y = H (wholeW selector xtra mask packets rows sources gamma hg hh p y)) ∧
      SourceSteps.EncWords (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p modeC ph).hT ℜ 𝔟 Hi Ai ∧
      Ai (Dims.encT (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p modeC ph).hT 5) =
        ZeroPadding.pad ℜ ((A (wholeW selector xtra mask packets rows sources gamma hg hh p (Dims.encT (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p modeC ph).hT 5))).take (InitRun.D0 𝔟)) ∧
      firstOutP5 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 (initW selector xtra mask packets rows sources gamma hg hh p modeC ph)
        (G7 mask packets rows sources gamma hg hh p modeC ph (𝔘 + 1) (Nat.le_succ _)).2 coordC ph ci 𝔏 tgtC modeC ℜ (InitS.Rk ℜ) 𝔟 layA factsA
        (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (fun _ => 0)
        ((𝔇).maskSlots_injective 𝒽1) ((𝔇).pslots_injective 𝒽1) ((𝔇).familySlots_injective 𝒽1) ((𝔇).poolSlots_injective 𝒽1)
        (rewind2_injective (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1) (hrawR mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 𝒽1) (hpoolR mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 𝒽1)
        (hsrcR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 𝒽1) (Fin.last 𝔘) (ℭ𝔖 modeC 15) 𝔔 (ℭ𝔖 modeC 17) (ℭ𝔖 modeC 18)
        (fun i => H (wholeW selector xtra mask packets rows sources gamma hg hh p i)) Hi (fun i => SourceSteps.queriedAt sources p den hden 𝔨 𝔯 𝔰 n x bits hp ci.val A (wholeW selector xtra mask packets rows sources gamma hg hh p i)) Ai
        𝔟 vMB vMS ℜ ℜ ℜ ℜ vWS vRW vBF 𝔟 vU0 (fuelOf 𝒞 𝔟 vdS0 0) firstCost H' A' := by
  -- the guard
  obtain ⟨Hi, Ai, hrun, hC, hlong, ⟨hq, hq17, hq18, h284, hH15, hH284, hH17, hH18⟩, hlow, -, hE, hpay⟩ :=
    StartA.guardEntry selector xtra mask packets rows sources gamma hg hh p modeC ph n x bits den hden hp (fun ph' => phaseE sources p den 𝔨 x bits modeC ph' 𝔏) ci.val hn hxtra hV1 hA A H hI.1 hI.2
  have hC0 : Rest.InvC (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 ℜ (InitS.Rk ℜ) (KcW selector xtra mask packets rows sources gamma hg hh p modeC) (K0W selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (fun _ => 0)
      (Fin.last 𝔘) 𝔟 vQ vMB vMS ℜ ℜ ℜ ℜ vWS vRW vBF 𝔟 vU0 Hi Ai := by
    rw [hA]; exact hC
  have hC' : Rest.InvC (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 ℜ (InitS.Rk ℜ) (KcW selector xtra mask packets rows sources gamma hg hh p modeC) (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (fun _ => 0)
      (Fin.last 𝔘) 𝔟 vQ vMB vMS ℜ ℜ ℜ ℜ vWS vRW vBF 𝔟 vU0 Hi Ai :=
    invC_congrK0 hC0 (fun y hy => K0W'_Kc selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val y hy)
  have hq3 := query_facts selector xtra mask packets rows sources gamma hg hh p modeC
  have hwq := pad_len selector xtra mask packets rows sources gamma hg hh p n x bits ci.val hqw
  -- the first seam
  obtain ⟨H', A', hfo⟩ := firstOut5_exists mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (se := (DSite selector mask packets rows sources gamma hg hh p).se) (sp := (DSite selector mask packets rows sources gamma hg hh p).sp) (e := (eSite selector xtra mask packets rows sources gamma hg hh p)) (hV := 𝒽1)
    (initM := initW selector xtra mask packets rows sources gamma hg hh p modeC ph) (g7M := (G7 mask packets rows sources gamma hg hh p modeC ph (𝔘 + 1) (Nat.le_succ _)).2)
    (g7cost := g7cost) (coordinate := coordC) (ph := ph) (ci := ci) (L := 𝔏) (target := tgtC) (mode := modeC) (Rc := ℜ) (Rk := InitS.Rk ℜ) (b := 𝔟)
    (layoutAt := layA) (capsAt := capsAt) (factsAt := factsA) (goodAt := goodAt)
    (K := KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (K0 := K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (KH0 := fun _ => 0) (hG7 := hG7)
    (hminj := (𝔇).maskSlots_injective 𝒽1) (hsinj := (𝔇).pslots_injective 𝒽1) (hfinj := (𝔇).familySlots_injective 𝒽1)
    (hpinj := (𝔇).poolSlots_injective 𝒽1) (hrinj := rewind2_injective (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1)
    (hraw := hrawR mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 𝒽1) (hpool := hpoolR mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 𝒽1)
    (hsrc := hsrcR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 𝒽1)
    (cnt := Fin.last 𝔘) (c15 := ℭ𝔖 modeC 15) (q284 := 𝔔) (c17 := ℭ𝔖 modeC 17) (c18 := ℭ𝔖 modeC 18) (hcnt := rfl)
    (hlow := hq3.1)
    (h1 := hq3.2.1)
    (h2 := hq3.2.2.1) (h3 := hq3.2.2.2.1)
    (h4 := hq3.2.2.2.2.1)
    (h5 := hq3.2.2.2.2.2.1)
    (h6 := hq3.2.2.2.2.2.2)
    (C := 𝔠𝔞𝔭) (wq := 𝔴𝔮) (hwq := hwq) (icost := 𝔦𝔠)
    (H0 := fun i => H (wholeW selector xtra mask packets rows sources gamma hg hh p i)) (Hi := Hi)
    (A0 := fun i => SourceSteps.queriedAt sources p den hden 𝔨 𝔯 𝔰 n x bits hp ci.val A (wholeW selector xtra mask packets rows sources gamma hg hh p i)) (Ai := Ai) (hinit := hrun)
    (Kc := KcW selector xtra mask packets rows sources gamma hg hh p modeC) (w := 𝔟) (Mb := vMB) (Ms := vMS) (cW := ℜ) (cQ := ℜ) (cB := ℜ) (cS := ℜ) (S := vWS) (Rw := vRW) (B := vBF)
    (v := 𝔟) (U0 := vU0) (fuel0 := fuelOf 𝒞 𝔟 vdS0 0) (hC := hC')
    (hRk := hRk) (hRc4 := hRc4) (hSl := hSl) (hRl := hRl) (hBl := hBl) (hvl := hvl) (hUl := hUl) (hMb := hMb) (hMs := hMs)
    (hKpos := hKpos) (hKsub := fun y hy h1 h2 => ⟨hy, h1, h2⟩) (hKcnt := hKcnt) (hKfree := hKfree) (hKr1 := hKr1) (hKr2 := hKr2)
    (hK15 := hK15) (hK284 := hK284)
    (hq := hq) (hq17 := hq17) (hq18 := hq18) (h284 := h284) (hH15 := hH15) (hH284 := hH284) (hH17 := hH17) (hH18 := hH18)
    (hlong := hlong) (hN := hN) (hlog := hlog) (he1 := he1) (hpw := hpw) (hfirst := hfirst) (hsecond := hsecond) (hdescR := hdescR)
    (hL := hL) (hfamH0 := hfamH0) (hwinI0 := hwinI0) (hwinZ0 := hwinZ0) (firstCost := firstCost) (hcost0 := hcost0)
  exact ⟨Hi, H', Ai, A', hlow, hE, hpay, hfo⟩

/-- **THE FIRST-ENTRY HOLE at the v5 site** (`StartHole4`, E2/E3/E4/E16). -/
theorem startHole5W_site (G7 : FirstW.G7W selector xtra) (hres : 19 ≤ 𝔯𝔢𝔰) (ph : Phase)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) s)
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p 𝔨 𝔯 𝔰) states)
    (ci : Fin (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC))
    (lay : TraceData.LayoutFamily coordC ph ci sources 𝔏 tgtC modeC selector)
    (K : Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Prop)
    (K0 : Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Nat)
    (dflt : P1TopDownPaidReusable.Datum)
    (Hd : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → List Bool)
    (familyCost firstCost counterReserve refillCost : Nat)
    (g7cost : ℕ → ℕ) (capsAt : ℕ → RowCaps)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordC ph ci 𝔏 tgtC modeC m) (layA m) (factsA m) (capsAt m))
    -- the onset and the site's scalar facts
    (hn : extraW selector xtra mask packets rows sources gamma hg hh p ≤ n)
    (hxtra : XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ xtra mask packets rows sources gamma hg hh p)
    (hV1 : 1 ≤ SourceBudget.Params.cVcN selector sources gamma hg hh p)
    (hA : vQ = 𝔮)
    (hqw : (SourceSteps.qwordAt sources p 𝔨 n x bits ci.val).length ≤ 𝔠𝔞𝔭)
    -- S's first-seam premises (static)
    (hG7 : ResidentRunH (G7 mask packets rows sources gamma hg hh p modeC ph (𝔘 + 1) (Nat.le_succ _)).2 g7cost mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots 𝒽1) ((𝔇).pslots 𝒽1) ((𝔇).slot 𝒽1) ((𝔇).ret 𝒽1) ((𝔇).scr 𝒽1 0) ((𝔇).scr 𝒽1 1)
      ((𝔇).familySlots 𝒽1) ((𝔇).poolSlots 𝒽1) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1)
      ((𝔇).scr 𝒽1 5) ((𝔇).scr 𝒽1 6) ((𝔇).scr 𝒽1 7) ((𝔇).scr 𝒽1 8) ((𝔇).scr 𝒽1 9) ((𝔇).scr 𝒽1 10)
      (Dims.lenTape (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1) coordC ph ci 𝔏 tgtC modeC ℜ 𝔟
      ((𝔇).pcT (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layA capsAt
      (Dims.Rpad (d := 𝔇) (eX := (DSite selector mask packets rows sources gamma hg hh p).se.extra) (pX := (DSite selector mask packets rows sources gamma hg hh p).sp.extra) (gW := (DSite selector mask packets rows sources gamma hg hh p).gW) (V := 𝔘 + 1) ℜ)
      (RestIn4 (𝔇) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ℜ ((𝔇).pcT (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 𝒽1 ⟨64, by unfold restPc; omega⟩) (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (fun _ => (0 : ℕ)))
      (fun y => OutV (𝔇) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW y.val))
    (hRk : ℜ ≤ (InitS.Rk ℜ))
    (hRc4 : 4 ≤ ℜ)
    (hSl : vWS + 2 ≤ ℜ)
    (hRl : vRW + 2 ≤ ℜ)
    (hBl : vBF + 2 ≤ ℜ)
    (hvl : 𝔟 + 2 ≤ ℜ)
    (hUl : vU0 ≤ ℜ)
    (hMb : vMB ≤ ℜ)
    (hMs : vMS ≤ ℜ)
    (hKpos : ∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ≤ y.val ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 10 ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 11))
    (hKcnt : ∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → y ≠ (Fin.last 𝔘))
    (hKfree : ∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → Cycle.Free ((𝔇).slot 𝒽1) ((𝔇).maskSlots 𝒽1) ((𝔇).pslots 𝒽1) ((𝔇).poolSlots 𝒽1)
      ((𝔇).familySlots 𝒽1) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1) y ∨
      y = Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1 ∨ y = Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2)
    (hKr1 : (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) →
      (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) = List.replicate (capsAt 0).descriptorReserve true ∧
      (fun _ => (0 : ℕ)) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) = 0)
    (hKr2 : (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) →
      (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) = List.replicate (capsAt 0).descriptorReserve false ∧
      (fun _ => (0 : ℕ)) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) = 0)
    (hK15 : (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (ℭ𝔖 modeC 15) → (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (ℭ𝔖 modeC 15) = List.replicate 𝔠𝔞𝔭 false ∧ (fun _ => (0 : ℕ)) (ℭ𝔖 modeC 15) = 0)
    (hK284 : (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) 𝔔 → (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) 𝔔 = 𝔴𝔮 ∧ (fun _ => (0 : ℕ)) 𝔔 = 0)
    (hN : (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordC ph ci).length).length ≤ ℜ)
    (hlog : 2 * ((requestAt coordC ph ci 𝔏 tgtC modeC 0).input (decompositionOf sources)).length + 1 ≤ ℜ)
    (he1 : 1 ≤ (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0))
    (hpw : (CloseoutRowsCountBinary.bits ((PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0))).length ≤ 𝔟)
    (hfirst : (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * 2^(natBitLength ((PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0))) < 2^𝔟)
    (hsecond : (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) * 2^(vQ+1) < 2^𝔟)
    (hdescR : (capsAt 0).descriptorReserve ≤ ℜ)
    (hL : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length + 3 ≤ ℜ)
    (hfamH0 : ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC 0)) (layA 0) (factsA 0)) vWS vRW vBF (dataList (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC 0)) (layA 0) (factsA 0)).length i + (fuelOf 𝒞 𝔟 vdS0 0) + 1 ≤ ℜ)
    (hwinI0 : g7cost 0 + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) (layA 0) (factsA 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF 𝔟 (0)) + 1 ≤ ℜ)
    (hwinZ0 : (g7cost 0 + 1 + backCost (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (requestAt coordC ph ci 𝔏 tgtC modeC 0) ℜ 𝔟 vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length vMB vMS) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) (layA 0) (factsA 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF 𝔟 (0)) + 1 ≤ (InitS.Rk ℜ))
    (hcost0 : (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci 𝔏 tgtC modeC 0) (layA 0) (factsA 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF 𝔟 (𝔦𝔠 + 1 + ((4*(InitS.Rk ℜ)+7) + 1 + (((4*ℜ+7) + 1 + ((4*ℜ+7) + 1 + ((2*𝔠𝔞𝔭+4) + 1 + (2*𝔠𝔞𝔭+4) + 1 + (2*𝔠𝔞𝔭+4)))) + 1 + ((g7cost 0 + 1 + backCost (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (requestAt coordC ph ci 𝔏 tgtC modeC 0) ℜ 𝔟 vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))).gs).length vMB vMS) + 1 + (refreshCost ℜ + 1 + ((2*ℜ+4) + 1 + 1))))))) ≤ firstCost)
    -- the call-0 row width (layout rows)
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg vQ 𝔏) (hL1 : 1 ≤ 𝔏)
    (hu : 1 ≤ vQ / (200 * (normalizedLiveCount vQ 𝔏 + 1 + 1)))
    -- the kept set on `U` (`first_startV`)
    (hKposU : ∀ y, K y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ≤ y.val ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽 10 ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽 11))
    (hK : ∀ y, K y → KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC y.castSucc)
    (hK0 : ∀ y, K y → K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val y.castSucc = K0 y ∧ (0 : ℕ) = KH0 y)
    (hKapp : ∀ y, K y → ∀ i, (𝒞).app i ≠ y)
    (hcR : counterReserve = ℜ) (h4b : 4 * 𝔟 + 5 ≤ ℜ) :
    SourceSteps.StartHole5 mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) g7F preFF compiler den hden n x bits hp site ci 𝔏 ℜ
      (InitS.Rk ℜ) 𝔟 lay K K0 KH0 𝔙 dflt Hd Ad familyCost firstCost counterReserve refillCost ℜ ℜ ℜ ℜ
      (EW selector xtra mask packets rows sources gamma hg hh p modeC n x bits) (fun ph' => phaseE sources p den 𝔨 x bits modeC ph' 𝔏) := by
  intro A H hI
  obtain ⟨Hi, H', Ai, A', hlow, hE, hpay, hfo⟩ := firstExit5W_site selector xtra mask packets rows sources gamma hg hh p G7 hres ph g7F compiler den hden n x bits hp site ci lay K K0 KH0 dflt Hd Ad familyCost firstCost counterReserve refillCost g7cost capsAt goodAt hn hxtra hV1 hA hqw hG7 hRk hRc4 hSl hRl hBl hvl hUl hMb hMs hKpos hKcnt hKfree hKr1 hKr2 hK15 hK284 hN hlog he1 hpw hfirst hsecond hdescR hL hfamH0 hwinI0 hwinZ0 hcost0 hlay hL1 hu hKposU hK hK0 hKapp hcR A H hI
  have hPW := hI.1.2.1
  have hW81 := (wd_queried selector xtra mask packets rows sources gamma hg hh p ph n x bits den hden hp ci.val A 81 (Or.inl rfl)).trans hPW.1
  have hW90 := (wd_queried selector xtra mask packets rows sources gamma hg hh p ph n x bits den hden hp ci.val A 90 (Or.inr rfl)).trans hPW.2.1
  refine ⟨H', A', ?_⟩
  exact StartB5.chainStart_first5 mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) g7F
    (fun ph' => ⟨_, initW selector xtra mask packets rows sources gamma hg hh p modeC ph'⟩) (fun ph' => G7 mask packets rows sources gamma hg hh p modeC ph' (𝔘 + 1) (Nat.le_succ _))
    (Fin.last 𝔘) (ℭ𝔖 modeC 15) 𝔔 (ℭ𝔖 modeC 17) (ℭ𝔖 modeC 18) compiler den hden n x bits hp site ci 𝔏 ℜ (InitS.Rk ℜ) 𝔟 lay K K0 KH0
    (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (fun _ => 0) 𝔙 dflt Hd Ad
    familyCost firstCost counterReserve refillCost ((A ((𝒞).whole (Dims.encT (d := 𝔇) 𝒽 5).castSucc)).take (InitRun.D0 𝔟))
    A H Hi H' Ai A' hfo hlow hE hpay hW81 hW90
    (fun y hy he => hy 15 (by rw [he]; exact cacheSite_val selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC 15)) rfl rfl
    (fun i hi j => app_not_cache selector xtra mask packets rows sources gamma hg hh p G7 hres ph modeC g7F i hi j) hlay hL1 hu hKposU hK hK0 hKapp hcR h4b

end site

end
end NearCubicWires.SourceSkeleton.StartC5W
end

