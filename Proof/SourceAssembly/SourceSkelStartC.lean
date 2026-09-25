import Proof.SourceAssembly.SourceSkelStartA
import Proof.SourceAssembly.SourceSkelStartB

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
namespace NearCubicWires.SourceSkeleton.StartC
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

/-- The query tapes lie below `F` and are pairwise distinct. -/
theorem query_facts (modeB : Bool) :
    ((ℭ𝔖 modeB 15).val < (𝔇).F ∧ (𝔔).val < (𝔇).F ∧ (ℭ𝔖 modeB 17).val < (𝔇).F ∧ (ℭ𝔖 modeB 18).val < (𝔇).F) ∧
    (ℭ𝔖 modeB 15) ≠ 𝔔 ∧ (ℭ𝔖 modeB 15) ≠ (ℭ𝔖 modeB 17) ∧ (ℭ𝔖 modeB 15) ≠ (ℭ𝔖 modeB 18) ∧
    𝔔 ≠ (ℭ𝔖 modeB 17) ∧ 𝔔 ≠ (ℭ𝔖 modeB 18) ∧ (ℭ𝔖 modeB 17) ≠ (ℭ𝔖 modeB 18) := by
  have hsn := site_nums selector xtra mask packets rows sources gamma hg hh p
  have hF : (𝔇).F = PCJda54a286946142d3_BranchPhases.offset sources p 𝔨 𝔯 + 1155 := hsn.1
  have v15 := cacheSite_val selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeB 15
  have v17 := cacheSite_val selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeB 17
  have v18 := cacheSite_val selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) modeB 18
  have n15 := cache_nums selector xtra mask packets rows sources gamma hg hh p modeB 15
  have n17 := cache_nums selector xtra mask packets rows sources gamma hg hh p modeB 17
  have n18 := cache_nums selector xtra mask packets rows sources gamma hg hh p modeB 18
  have v284 : (𝔔).val = 284 := rfl
  have a15 : (ℭ𝔖 modeB 15).val ≠ 284 := by rw [v15]; omega
  have a17 : (ℭ𝔖 modeB 17).val ≠ 284 := by rw [v17]; omega
  have a18 : (ℭ𝔖 modeB 18).val ≠ 284 := by rw [v18]; omega
  have cinj := PCJ30aa6f1b7c2a4221_.Selected.cache_injective sources p 𝔨 𝔯 𝔰 modeB
  have hne : ∀ i j : Fin 19, i ≠ j → (ℭ𝔖 modeB i) ≠ (ℭ𝔖 modeB j) := by
    intro i j hij he
    have hv := congrArg Fin.val he
    rw [cacheSite_val, cacheSite_val] at hv
    exact hij (cinj (Fin.ext hv))
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun he => a15 (by rw [he]; exact v284), hne 15 17 (by decide), hne 15 18 (by decide),
    fun he => a17 (by rw [← he]; exact v284), fun he => a18 (by rw [← he]; exact v284), hne 17 18 (by decide)⟩
  · rw [v15]; omega
  · rw [v284]; omega
  · rw [v17]; omega
  · rw [v18]; omega

/-- The query word padded to the cache capacity has exactly that length. -/
theorem pad_len (n : ℕ) (x : BitInput n) (bits : List Bool) (c : ℕ)
    (hqw : (SourceSteps.qwordAt sources p 𝔨 n x bits c).length ≤ capC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
      (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits)) :
    (ZeroPadding.pad (capC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))
      (SourceSteps.qwordAt sources p 𝔨 n x bits c)).length =
      capC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate]
  omega

/-- The phase word slots are off the cache, so the queried bank shows the entry's words there. -/
theorem wd_queried (ph : Phase) (n : Nat) (x : BitInput n) (bits : List Bool) (den : Nat) (hden : 0 < den)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (c : ℕ) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p 𝔨 𝔯 𝔰) → List Bool) (i : Fin 278) (hi : i.val = 81 ∨ i.val = 90) :
    SourceSteps.queriedAt sources p den hden 𝔨 𝔯 𝔰 n x bits hp c A (SourceParent.Wd sources p 𝔨 𝔯 𝔰 ph i) =
      A (SourceParent.Wd sources p 𝔨 𝔯 𝔰 ph i) := by
  refine SourceSteps.queriedAt_off sources p den hden 𝔨 𝔯 𝔰 n x bits hp c A _ (fun j => ?_)
  have hw := wd_val mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 ph i (by omega) (by omega)
  have hs := NearCubicWires.SourcePhase.size_302 sources p 𝔨 𝔯
  refine NearCubicWires.SourceStart.Pen0.not_cache sources p den hden 𝔨 𝔯 𝔰 n x bits hp _ ?_ j
  rcases hw with h | h
  · left; rw [h]; omega
  · right; rw [h]; omega

/-- The code's `app` tapes below `F` (the phase word slots) are off the cache. -/
theorem app_not_cache (G7 : FirstW.G7W selector xtra) (hres : 19 ≤ 𝔯𝔢𝔰) (ph : Phase) (modeB : Bool)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) s)
    (i : Fin 6) (hi : ((skelCodeR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2)
      (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph)).app i).val < (𝔇).F) (j : Fin 19) :
    ((skelCodeR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2)
      (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph)).app i).val ≠
      (PCJda54a286946142d3_BranchPhases.cache sources p 𝔨 𝔯 𝔰 modeB j).val := by
  have hsn := site_nums selector xtra mask packets rows sources gamma hg hh p
  have hF : (𝔇).F = PCJda54a286946142d3_BranchPhases.offset sources p 𝔨 𝔯 + 1155 := hsn.1
  have hc := cache_nums selector xtra mask packets rows sources gamma hg hh p modeB j
  have hs := NearCubicWires.SourcePhase.size_302 sources p 𝔨 𝔯
  have hrt : 19 ≤ r_tapes (printerOf sources) := by unfold r_tapes; omega
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5) with h | h | h | h | h | h
  · have ei : i = 0 := Fin.ext h
    subst ei
    have e6 := enc6_app0 mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph)
    have hv := enc_val_R mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph) 6 (by decide)
    rw [← e6] at hi ⊢
    rw [hv] at hi ⊢
    simp only [show (6 : Fin 11).val = 6 from rfl, if_neg (show ¬ (6 : ℕ) < 5 by decide)] at hi ⊢
    omega
  · have ei : i = 1 := Fin.ext h
    subst ei
    have hv := StartB.app1_wd mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph)
    have hw := wd_val mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 ph 81 (by decide) (by decide)
    rw [hv]
    rcases hw with h' | h' <;> rw [h'] <;> omega
  · have ei : i = 2 := Fin.ext h
    subst ei
    have hv := congrArg Fin.val (StartB.app2_encT mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph))
    rw [Fin.val_castSucc, StartB.encT1_val] at hv
    rw [hv] at hi; omega
  · have ei : i = 3 := Fin.ext h
    subst ei
    have hv := StartB.app3_wd mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph)
    have hw := wd_val mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 ph 90 (by decide) (by decide)
    rw [hv]
    rcases hw with h' | h' <;> rw [h'] <;> omega
  · have ei : i = 4 := Fin.ext h
    subst ei
    have hv := congrArg Fin.val (StartB.app4_encT mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph))
    rw [Fin.val_castSucc, StartB.encT1_val] at hv
    rw [hv] at hi; omega
  · have ei : i = 5 := Fin.ext h
    subst ei
    have hv := congrArg Fin.val (StartB.app5_encT mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (firstW selector xtra G7 mask packets rows sources gamma hg hh p modeB ph))
    rw [Fin.val_castSucc, StartB.encT1_val] at hv
    rw [hv] at hi; omega

end site

end
end NearCubicWires.SourceSkeleton.StartC
end

