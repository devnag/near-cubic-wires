import Proof.SourceAssembly.SourceRequestSelStartKept
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
namespace NearCubicWires.SourceRequest.SelStartKept2
open NearCubicWires.SourceRequest.SelStartKept
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

/-- A kept word off cache tape 15 does not see the cache-15 word. -/
theorem K0Site_update15 (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool) (w : List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) (y : Fin V) (hy : y ≠ cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode 15) :
    K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW (Function.update cdW 15 w) resW Vv NC y = K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC y := by
  by_cases hc : ∃ i, cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode i = y
  · obtain ⟨i, rfl⟩ := hc
    have hi : i ≠ 15 := fun h => hy (by rw [h])
    rw [K0Site_cache, K0Site_cache, Function.update_of_ne hi]
  · have hx : ∀ i, (PCJda54a286946142d3_BranchPhases.cache sources p 𝔨 𝔯 𝔰 mode i).val ≠ y.val :=
      fun i h => hc ⟨i, Fin.ext (by rw [cacheSite_val]; exact h)⟩
    rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW _ resW Vv NC y hx, K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW _ resW Vv NC y hx]

theorem startKept_site' (G7 : FirstW.G7W selector xtra) (hres : 19 ≤ 𝔯𝔢𝔰) (ph : Phase)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) s)
    (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (ci : Fin (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC))
    (capsAt : ℕ → RowCaps) (hcaps0 : (capsAt 0).descriptorReserve = 𝔙) :
    (∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ≤ y.val ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 10 ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽1 11)) ∧
    (∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → y ≠ (Fin.last 𝔘)) ∧
    (∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) y → Cycle.Free ((𝔇).slot 𝒽1) ((𝔇).maskSlots 𝒽1) ((𝔇).pslots 𝒽1) ((𝔇).poolSlots 𝒽1)
      ((𝔇).familySlots 𝒽1) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1) y ∨
      y = Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1 ∨ y = Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) ∧
    ((KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) →
      (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) = List.replicate (capsAt 0).descriptorReserve true ∧
      (fun _ => (0 : ℕ)) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 1) = 0) ∧
    ((KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) →
      (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) = List.replicate (capsAt 0).descriptorReserve false ∧
      (fun _ => (0 : ℕ)) (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext 𝒽1 2) = 0) ∧
    ((KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) (ℭ𝔖 modeC 15) → (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (ℭ𝔖 modeC 15) = List.replicate 𝔠𝔞𝔭 false ∧ (fun _ => (0 : ℕ)) (ℭ𝔖 modeC 15) = 0) ∧
    ((KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC) 𝔔 → (K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) 𝔔 = 𝔴𝔮 ∧ (fun _ => (0 : ℕ)) 𝔔 = 0) ∧
    (∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) modeC) y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ≤ y.val ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽 10 ∧ y ≠ Dims.hrT (eSite selector xtra mask packets rows sources gamma hg hh p) 𝒽 11)) ∧
    (∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) modeC) y → KSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC y.castSucc) ∧
    (∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) modeC) y → K0W' selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val y.castSucc = (K0Site selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) modeC (RepairOrdinary.frame bits) 𝔴𝔮 (Function.update (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) 15 (List.replicate 𝔠𝔞𝔭 false)) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC)) y ∧ (0 : ℕ) = (fun _ => (0 : ℕ)) y) ∧
    (∀ y, (KSite selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) modeC) y → ∀ i, (𝒞).app i ≠ y) := by
  have hU1 : (𝔡).U ≤ 𝔘 + 1 := Nat.le_succ _
  have c15v := cacheSite_val selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeC 15
  have c15r := cache_nums selector xtra mask packets rows sources gamma hg hh p modeC 15
  have off15 : ∀ y : Fin (𝔘 + 1), y.val = 278 ∨ y.val = 279 ∨ y.val = 284 → y ≠ ℭ𝔖 modeC 15 := fun y hy h => by
    have := congrArg Fin.val h; rw [c15v] at this; omega
  refine ⟨fun y hy => KSite_pos selector xtra mask packets rows sources gamma hg hh p _ _ modeC y hy, fun y hy => KSite_cnt selector xtra mask packets rows sources gamma hg hh p modeC y hy,
    fun y hy => KSite_free selector xtra mask packets rows sources gamma hg hh p _ _ modeC y hy, fun _ => ⟨?_, rfl⟩, fun _ => ⟨?_, rfl⟩, fun _ => ⟨?_, rfl⟩, fun _ => ⟨?_, rfl⟩,
    fun y hy => KSite_pos selector xtra mask packets rows sources gamma hg hh p _ _ modeC y hy, fun y hy => KSite_castSucc selector xtra mask packets rows sources gamma hg hh p _ _ _ modeC y hy,
    fun y hy => ⟨?_, rfl⟩, fun y hy i h => KSite_app selector xtra mask packets rows sources gamma hg hh p _ _ modeC ph y hy i (by rw [← h]; rfl)⟩
  · show Function.update (K0W selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (ℭ𝔖 modeC 15) (List.replicate 𝔠𝔞𝔭 false) _ = _
    rw [Function.update_of_ne (off15 _ (Or.inl rfl))]
    show K0Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) modeC (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) _ = _
    rw [hcaps0]; exact (K0Site_rew selector xtra mask packets rows sources gamma hg hh p _ _ modeC (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC)).1
  · show Function.update (K0W selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (ℭ𝔖 modeC 15) (List.replicate 𝔠𝔞𝔭 false) _ = _
    rw [Function.update_of_ne (off15 _ (Or.inr (Or.inl rfl)))]
    show K0Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) modeC (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) _ = _
    rw [hcaps0]; exact (K0Site_rew selector xtra mask packets rows sources gamma hg hh p _ _ modeC (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC)).2
  · show Function.update (K0W selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (ℭ𝔖 modeC 15) (List.replicate 𝔠𝔞𝔭 false) (ℭ𝔖 modeC 15) = _
    exact Function.update_self _ _ _
  · show Function.update (K0W selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (ℭ𝔖 modeC 15) (List.replicate 𝔠𝔞𝔭 false) _ = _
    rw [Function.update_of_ne (off15 _ (Or.inr (Or.inr rfl)))]
    show K0Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) modeC (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) _ = _
    exact K0Site_284 selector xtra mask packets rows sources gamma hg hh p _ _ modeC (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC)
  · show Function.update (K0W selector xtra mask packets rows sources gamma hg hh p modeC n x bits ph ci.val) (ℭ𝔖 modeC 15) (List.replicate 𝔠𝔞𝔭 false) y.castSucc = _
    by_cases h15 : y = cacheSite selector xtra mask packets rows sources gamma hg hh p _ (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) modeC 15
    · have e : y.castSucc = ℭ𝔖 modeC 15 := by
        rw [h15]; exact Fin.ext (by rw [Fin.val_castSucc, cacheSite_val, cacheSite_val])
      rw [e, Function.update_self, h15, K0Site_cache, Function.update_self]
    · have e : y.castSucc ≠ ℭ𝔖 modeC 15 := fun h => h15 (Fin.ext (by
        have := congrArg Fin.val h; rw [Fin.val_castSucc, cacheSite_val] at this; rw [this, cacheSite_val]))
      rw [Function.update_of_ne e, K0Site_update15 selector xtra mask packets rows sources gamma hg hh p _ _ modeC _ _ _ _ _ _ _ y h15]
      show K0Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) modeC (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) y.castSucc = _
      exact K0Site_castSucc selector xtra mask packets rows sources gamma hg hh p _ _ _ modeC (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci.val) (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeC n 𝔟) 𝔙 (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC) y

end site

end
end NearCubicWires.SourceRequest.SelStartKept2
end
