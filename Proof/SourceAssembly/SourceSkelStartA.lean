import Proof.SourceAssembly.SourceSkelGuardG
import Proof.Packets.SrcEntryW

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
namespace NearCubicWires.SourceSkeleton.StartA
open NearCubicWires.SourceSkeleton.KeptW NearCubicWires.SourceSkeleton.GuardG NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔰" => scrSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔘" => USite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔭𝔩" => plSite selector xtra mask packets rows sources gamma hg hh p mode ph
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
local notation "𝔒" => C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits
set_option hygiene false in
local notation "𝔅𝔗" => ControllerSelectedContinuation.bodyTapes sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "ℭ𝔖" => cacheSite selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)
set_option hygiene false in
local notation "𝔔" => q284Site selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)
set_option hygiene false in
local notation "𝔟" => C10PartsSchedule.entryWidthSchedule sources (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) n
set_option hygiene false in
local notation "𝔠𝔞𝔭" => capC sources (kSite selector xtra mask packets rows sources gamma hg hh p) (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) x
  (C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits)
set_option hygiene false in
local notation "𝔴𝔮" => ZeroPadding.pad 𝔠𝔞𝔭 (SourceSteps.qwordAt sources p (kSite selector xtra mask packets rows sources gamma hg hh p) n x bits ci)
set_option hygiene false in
local notation "𝔄" => fun i => SourceSteps.queriedAt sources p den hden (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) n x bits hp ci A
  (wholeW selector xtra mask packets rows sources gamma hg hh p i)
set_option hygiene false in
local notation "ℌ" => fun i => H (wholeW selector xtra mask packets rows sources gamma hg hh p i)
set_option hygiene false in
local notation "𝔦𝔠" => InitS.initAllXCostE (plSite selector xtra mask packets rows sources gamma hg hh p mode ph) 𝔏 1
  (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p)
  (rC sources gamma hg hh p) (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1 (ldE sources gamma hg hh p)
  (ldC sources gamma hg hh p) mode (SourceBudget.Params.tgOf sources gamma hg hh p) 𝔮 𝔟 (dE sources gamma hg hh p)
  (dC sources gamma hg hh p) (cwE sources gamma hg hh p) (cwC sources gamma hg hh p)
  (NearCubicWires.SourceStart.MetaStepGF.metaCostG selector sources p packets 𝔏 𝔮) + 2

/-- The phase width fits the init's arity window: `tf + (q+1)^r ≤ (tf+1)(q+1)^r`. -/
theorem b_le (n : ℕ) :
    𝔟 ≤ (C10PartsSchedule.thresholdFloor sources + 1) * (𝔮 + 1)^(SourceSteps.rBsel sources p) := by
  show C10PartsSchedule.thresholdFloor sources + (𝔮 + 1)^(SourceSteps.rBsel sources p) ≤ _
  have h1 : 1 ≤ (𝔮 + 1)^(SourceSteps.rBsel sources p) := Nat.one_le_pow _ _ (by omega)
  generalize (𝔮 + 1)^(SourceSteps.rBsel sources p) = P at h1 ⊢
  generalize C10PartsSchedule.thresholdFloor sources = T
  nlinarith

/-- Truncating a padded word below its reserve and re-padding gives it back. -/
theorem pad_take_pad (R d : ℕ) (w : List Bool) (h : w.length ≤ d) :
    ZeroPadding.pad R ((ZeroPadding.pad R w).take d) = ZeroPadding.pad R w := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold ZeroPadding.pad
  rw [List.take_append, List.take_replicate]
  simp only [List.length_append, List.length_replicate, List.append_assoc, List.replicate_append_replicate]
  rw [List.take_of_length_le (by omega : w.length ≤ w.length + m)]
  congr 2
  omega

theorem guardFirstSite3 (mode : Bool) (ph : Phase) (n : ℕ)
    (hn : extraW selector xtra mask packets rows sources gamma hg hh p ≤ n)
    (hxtra : XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ xtra mask packets rows sources gamma hg hh p)
    (b : ℕ) (hb : b ≤ (C10PartsSchedule.thresholdFloor sources + 1) * (𝔮 + 1)^(SourceSteps.rBsel sources p))
    (hV1 : 1 ≤ SourceBudget.Params.cVcN selector sources gamma hg hh p)
    (frameW qW : List Bool) (cdW : Fin 19 → List Bool) (NC C : ℕ) (wq : List Bool)
    (H0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → ℕ) (A0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool)
    (hd : A0 ((𝔡).scr (𝔭𝔩).hT 11) = [])
    (hAr : A0 (𝔭𝔩).ar = UnaryTemplate.tape 𝔮) (hHr : H0 (𝔭𝔩).ar = 0)
    (hAw : A0 (𝔭𝔩).wd = List.replicate b true) (hHw : H0 (𝔭𝔩).wd = 0)
    (hres : ∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), 278 ≤ x.val → x.val < 284 →
      (A0 x).length ≤ WorkspaceSelectedEntryBudget.envelope sources p (kW selector mask packets rows sources gamma hg hh p) (SourceSteps.rBsel sources p) n + 1 ∧ H0 x = 0)
    (hF : ∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), (𝔡).F ≤ x.val → x.val < (𝔡).U → A0 x = [] ∧ H0 x = 0)
    (hK8 : ∀ x, KcSiteG selector xtra mask packets rows sources gamma hg hh p mode x → x.val < (𝔡).F → (x.val < 278 ∨ 285 ≤ x.val) →
      A0 x = K0SG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC x ∧ H0 x = 0)
    (hcntA : (A0 (Fin.last _)).length ≤ ℜ) (hcntH : H0 (Fin.last _) ≤ ℜ)
    (hq : A0 (c15SG selector xtra mask packets rows sources gamma hg hh p mode) = wq) (hq17 : A0 (c17SG selector xtra mask packets rows sources gamma hg hh p mode) = List.replicate C true)
    (hq18 : A0 (c18SG selector xtra mask packets rows sources gamma hg hh p mode) = List.replicate (C+1) false) (h284 : (A0 (q284SG selector xtra mask packets rows sources gamma hg hh p)).length ≤ C)
    (hH15 : H0 (c15SG selector xtra mask packets rows sources gamma hg hh p mode) = 0) (hH284 : H0 (q284SG selector xtra mask packets rows sources gamma hg hh p) = 0) (hH17 : H0 (c17SG selector xtra mask packets rows sources gamma hg hh p mode) = 0)
    (hH18 : H0 (c18SG selector xtra mask packets rows sources gamma hg hh p mode) = 0) :
    ∃ (Hi : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → ℕ) (Ai : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool),
      Step (initW selector xtra mask packets rows sources gamma hg hh p mode ph)
        (InitS.initAllXCostE (𝔭𝔩) 𝔏 1 (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p)
          (rC sources gamma hg hh p) (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1 (ldE sources gamma hg hh p)
          (ldC sources gamma hg hh p) mode (SourceBudget.Params.tgOf sources gamma hg hh p) 𝔮 b (dE sources gamma hg hh p)
          (dC sources gamma hg hh p) (cwE sources gamma hg hh p) (cwC sources gamma hg hh p)
          (NearCubicWires.SourceStart.MetaStepGF.metaCostG selector sources p packets 𝔏 𝔮) + 2) H0 A0 Hi Ai ∧
      Rest.InvC (eSite selector xtra mask packets rows sources gamma hg hh p) (𝔭𝔩).hT ℜ (InitS.Rk ℜ) (KcSiteG selector xtra mask packets rows sources gamma hg hh p mode) (K0SG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC) (fun _ => 0)
        (Fin.last _) b 𝔮 (Mb 𝔏 𝔮) (InitPost.Ms 𝔏 𝔮) ℜ ℜ ℜ ℜ
        (sC sources gamma hg hh p * (𝔙 + 1)) (rC sources gamma hg hh p * (𝔙 + 1)) (𝔙 + 1) b (U0 𝔏 𝔮) Hi Ai ∧
      (∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), (𝔡).F ≤ x.val → x.val < (𝔡).U → ℜ ≤ (Ai x).length) ∧
      Ai (c15SG selector xtra mask packets rows sources gamma hg hh p mode) = wq ∧ Ai (c17SG selector xtra mask packets rows sources gamma hg hh p mode) = List.replicate C true ∧
      Ai (c18SG selector xtra mask packets rows sources gamma hg hh p mode) = List.replicate (C+1) false ∧ (Ai (q284SG selector xtra mask packets rows sources gamma hg hh p)).length ≤ C ∧
      Hi (c15SG selector xtra mask packets rows sources gamma hg hh p mode) = 0 ∧ Hi (q284SG selector xtra mask packets rows sources gamma hg hh p) = 0 ∧ Hi (c17SG selector xtra mask packets rows sources gamma hg hh p mode) = 0 ∧ Hi (c18SG selector xtra mask packets rows sources gamma hg hh p mode) = 0 ∧
      (∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), x.val < (𝔡).F → (x.val < 278 ∨ 284 ≤ x.val) → Ai x = A0 x ∧ Hi x = H0 x) ∧
      (∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), (𝔡).U ≤ x.val → Ai x = A0 x ∧ Hi x = H0 x) ∧
      SourceSteps.EncWords (d := 𝔡) (𝔭𝔩).hT ℜ b Hi Ai ∧ Ai (Dims.encT (d := 𝔡) (𝔭𝔩).hT 5) = List.replicate ℜ false := by
  obtain ⟨hFn, ho, hB, hU, hresn, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  have hlast : (Fin.last (USite selector xtra mask packets rows sources gamma hg hh p)).val = (𝔡).U := rfl
  obtain ⟨Hi, Ai, s, hC, hlong, hlowF, habove, henc⟩ := entry_initSite2G selector xtra mask packets rows sources gamma hg hh p mode ph n hn hxtra b hb hV1 H0 A0 hd hAr hHr hAw hHw hres hF
    (KcSiteG selector xtra mask packets rows sources gamma hg hh p mode) (K0SG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC) (fun _ => 0) (Fin.last _) (le_of_eq hlast.symm)
    (fun x hx hxF h8 h9 => by
      have hl := kc_lowG selector xtra mask packets rows sources gamma hg hh p mode x hx hxF h8 h9
      obtain ⟨e1, e2⟩ := hK8 x hx hxF hl
      exact ⟨by omega, e1, e2⟩)
    (fun x hx h8 => ⟨(k0s_rewG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC x).1 h8, rfl⟩)
    (fun x hx h9 => ⟨(k0s_rewG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC x).2 h9, rfl⟩)
    (fun x hx hxF => by
      obtain ⟨i, hi, hxv, hk⟩ := k0s_highG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC x hx hxF
      exact ⟨i, hi, hxv, hk, rfl⟩)
    hcntA hcntH
  have c15 := cache_nums selector xtra mask packets rows sources gamma hg hh p mode 15
  have c17 := cache_nums selector xtra mask packets rows sources gamma hg hh p mode 17
  have c18 := cache_nums selector xtra mask packets rows sources gamma hg hh p mode 18
  have v15 := cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 15
  have v17 := cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 17
  have v18 := cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 18
  have v284 : (q284SG selector xtra mask packets rows sources gamma hg hh p).val = 284 := rfl
  obtain ⟨a15, b15⟩ := hlowF (c15SG selector xtra mask packets rows sources gamma hg hh p mode) (by rw [v15]; omega) (by rw [v15]; omega)
  obtain ⟨a17, b17⟩ := hlowF (c17SG selector xtra mask packets rows sources gamma hg hh p mode) (by rw [v17]; omega) (by rw [v17]; omega)
  obtain ⟨a18, b18⟩ := hlowF (c18SG selector xtra mask packets rows sources gamma hg hh p mode) (by rw [v18]; omega) (by rw [v18]; omega)
  obtain ⟨a284, b284⟩ := hlowF (q284SG selector xtra mask packets rows sources gamma hg hh p) (by rw [v284]; omega) (by rw [v284]; omega)
  refine ⟨Hi, Ai, s, hC, hlong, a15.trans hq, a17.trans hq17, a18.trans hq18,
    (Nat.le_of_eq (congrArg List.length a284)).trans h284, b15.trans hH15, b284.trans hH284, b17.trans hH17,
    b18.trans hH18, hlowF, habove, encWords_of_encOut2G selector xtra mask packets rows sources gamma hg hh p mode ph _ b Hi Ai henc, (henc.1.2.2.2.2.2.2.2.2 5 (Or.inr rfl)).1⟩

/-- **The guard at any clause entry of `EW`.** -/
theorem guardEntry (mode : Bool) (ph : Phase) (n : ℕ) (x : BitInput n) (bits : List Bool) (den : ℕ) (hden : 0 < den)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (EF : Phase → Fin (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) → List CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (ci : ℕ)
    (hn : extraW selector xtra mask packets rows sources gamma hg hh p ≤ n)
    (hxtra : XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ xtra mask packets rows sources gamma hg hh p)
    (hV1 : 1 ≤ SourceBudget.Params.cVcN selector sources gamma hg hh p)
    (hA : (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒).arity = 𝔮)
    (A : Fin 𝔅𝔗 → List Bool) (H : Fin 𝔅𝔗 → ℕ)
    (hinv : SourceSteps.entryInvAt3 sources p den hden 𝔨 𝔯 𝔰 n x bits hp (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits) EF ph ci A H)
    (h284 : ph = .penalty ∧ ci = 0 → ((𝔄) 𝔔).length ≤ 𝔠𝔞𝔭) :
    ∃ (Hi : Fin (𝔘 + 1) → ℕ) (Ai : Fin (𝔘 + 1) → List Bool),
      Step (initW selector xtra mask packets rows sources gamma hg hh p mode ph) 𝔦𝔠 (ℌ) (𝔄) Hi Ai ∧
      Rest.InvC (eSite selector xtra mask packets rows sources gamma hg hh p) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT ℜ (InitS.Rk ℜ)
        (KcW selector xtra mask packets rows sources gamma hg hh p mode) (K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci) (fun _ => 0)
        (Fin.last _) 𝔟 𝔮 (Mb 𝔏 𝔮) (InitPost.Ms 𝔏 𝔮) ℜ ℜ ℜ ℜ
        (sC sources gamma hg hh p * (𝔙 + 1)) (rC sources gamma hg hh p * (𝔙 + 1)) (𝔙 + 1) 𝔟 (U0 𝔏 𝔮) Hi Ai ∧
      (∀ y : Fin (𝔘 + 1), (𝔡).F ≤ y.val → y.val < (𝔡).U → ℜ ≤ (Ai y).length) ∧
      InitS.QueryAt (ℭ𝔖 mode 15) 𝔔 (ℭ𝔖 mode 17) (ℭ𝔖 mode 18) 𝔠𝔞𝔭 𝔴𝔮 Hi Ai ∧
      (∀ y : Fin (𝔘 + 1), y.val < (𝔡).F → (y.val < 278 ∨ 284 ≤ y.val) → Ai y = (𝔄) y ∧ Hi y = (ℌ) y) ∧
      (∀ y : Fin (𝔘 + 1), (𝔡).U ≤ y.val → Ai y = (𝔄) y ∧ Hi y = (ℌ) y) ∧
      SourceSteps.EncWords (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT ℜ 𝔟 Hi Ai ∧
      Ai (Dims.encT (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT 5) =
        ZeroPadding.pad ℜ ((A (wholeW selector xtra mask packets rows sources gamma hg hh p
          (Dims.encT (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT 5))).take (InitRun.D0 𝔟)) := by
  -- the carried payload tape is off the cache
  have hnc : ∀ i, wholeW selector xtra mask packets rows sources gamma hg hh p
      (Dims.encT (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT 5) ≠
      PCJda54a286946142d3_BranchPhases.cache sources p 𝔨 𝔯 𝔰 (PCJ374c44bb8b7f47d9_.S.mode sources p den hden 𝔨 𝔯 𝔰 n x bits hp) i := by
    have hF := (site_nums selector xtra mask packets rows sources gamma hg hh p).1
    refine NearCubicWires.SourceStart.Pen0.not_cache sources p den hden 𝔨 𝔯 𝔰 n x bits hp _ (Or.inr ?_)
    show _ ≤ (𝔡).F + (𝔡).rt + 5
    rw [hF]; omega
  have hq5 := SourceSteps.queriedAt_off sources p den hden 𝔨 𝔯 𝔰 n x bits hp ci A _ (hnc)
  obtain ⟨h2, -, henc⟩ := hinv
  by_cases hfirst : ph = .penalty ∧ ci = 0
  · -- the first entry: the one-time init
    have h2' := h2
    unfold SourceSteps.entryInvAt2 at h2'
    rw [if_pos hfirst] at h2'
    obtain ⟨⟨hq, hq17, hq18, hH15, hH284, hH17, hH18⟩, hd, hAr, hHr, hAw, hHw, hres, hF, hK8, hcntA, hcntH⟩ := h2'
    have hd' : (𝔄) ((𝔡).scr (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT 11) = [] := hd
    have hAr' : (𝔄) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).ar = UnaryTemplate.tape 𝔮 := by
      have e : (𝔄) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).ar =
          UnaryTemplate.tape (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒).arity := hAr
      rw [e, hA]
    have hHr' : (ℌ) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).ar = 0 := hHr
    have hAw' : (𝔄) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).wd = List.replicate 𝔟 true := hAw
    have hHw' : (ℌ) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).wd = 0 := hHw
    have hres' : ∀ y : Fin (𝔘 + 1), 278 ≤ y.val → y.val < 284 →
        ((𝔄) y).length ≤ WorkspaceSelectedEntryBudget.envelope sources p (kW selector mask packets rows sources gamma hg hh p) (SourceSteps.rBsel sources p) n + 1 ∧ (ℌ) y = 0 :=
      fun y h1 h2 => hres y h1 (by omega)
    have hF' : ∀ y : Fin (𝔘 + 1), (𝔡).F ≤ y.val → y.val < (𝔡).U → (𝔄) y = [] ∧ (ℌ) y = 0 := hF
    have hK8' : ∀ y, KcSiteG selector xtra mask packets rows sources gamma hg hh p mode y → y.val < (𝔡).F → (y.val < 278 ∨ 285 ≤ y.val) →
        (𝔄) y = K0SG selector xtra mask packets rows sources gamma hg hh p mode n 𝔟 (RepairOrdinary.frame bits) 𝔴𝔮
          (SourceSteps.cdAt sources p 𝔨 n x bits ci) (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) y ∧ (ℌ) y = 0 := by
      intro y hy hyF hy2
      have h := hK8 y hy hyF hy2
      rw [ew_K0_eq] at h
      exact h
    have hcntA' : ((𝔄) (Fin.last _)).length ≤ ℜ := hcntA
    have hcntH' : (ℌ) (Fin.last _) ≤ ℜ := hcntH
    have hq' : (𝔄) (ℭ𝔖 mode 15) = 𝔴𝔮 := hq
    have hq17' : (𝔄) (ℭ𝔖 mode 17) = List.replicate 𝔠𝔞𝔭 true := hq17
    have hq18' : (𝔄) (ℭ𝔖 mode 18) = List.replicate (𝔠𝔞𝔭 + 1) false := hq18
    have hH15' : (ℌ) (ℭ𝔖 mode 15) = 0 := hH15
    have hH284' : (ℌ) 𝔔 = 0 := hH284
    have hH17' : (ℌ) (ℭ𝔖 mode 17) = 0 := hH17
    have hH18' : (ℌ) (ℭ𝔖 mode 18) = 0 := hH18
    obtain ⟨Hi, Ai, hrun, hC, hlong, a15, a17, a18, a284, b15, b284, b17, b18, hlow, hhigh, hE, a5⟩ :=
      guardFirstSite3 selector xtra mask packets rows sources gamma hg hh p mode ph n hn hxtra 𝔟
        (b_le selector xtra mask packets rows sources gamma hg hh p n) hV1
        (RepairOrdinary.frame bits) 𝔴𝔮 (SourceSteps.cdAt sources p 𝔨 n x bits ci) (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) 𝔠𝔞𝔭 𝔴𝔮
        (ℌ) (𝔄) hd' hAr' hHr' hAw' hHw' hres' hF' hK8' hcntA' hcntH' hq' hq17' hq18' (h284 hfirst) hH15' hH284' hH17' hH18'
    refine ⟨Hi, Ai, hrun, hC, hlong, ⟨a15, a17, a18, a284, b15, b284, b17, b18⟩, hlow, hhigh, hE, ?_⟩
    have h0 : A (wholeW selector xtra mask packets rows sources gamma hg hh p
        (Dims.encT (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT 5)) = [] := by
      rw [← hq5]
      have hU := (site_nums selector xtra mask packets rows sources gamma hg hh p).2.2.1
      have hU2 := (site_nums selector xtra mask packets rows sources gamma hg hh p).2.2.2.1
      refine (hF' _ ?_ ?_).1
      · show (𝔡).F ≤ (𝔡).F + (𝔡).rt + 5
        omega
      · show (𝔡).F + (𝔡).rt + 5 < (𝔡).U
        omega
    rw [a5, h0]
    simp [ZeroPadding.pad]
  · -- a later entry: the guard skips
    have h2' := h2
    unfold SourceSteps.entryInvAt2 at h2'
    rw [if_neg hfirst] at h2'
    obtain ⟨hQ, hL⟩ := h2'
    have eK0 : (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).K0 ph ci =
        K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci :=
      funext (fun y => ew_K0_eq selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci y)
    rw [eK0] at hL
    have hrun := guardLaterSiteG selector xtra mask packets rows sources gamma hg hh p mode ph n hn
      (KcW selector xtra mask packets rows sources gamma hg hh p mode) (K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci) (fun _ => 0)
      𝔟 (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒).arity (Mb 𝔏 𝔮) (InitPost.Ms 𝔏 𝔮)
      (sC sources gamma hg hh p * (𝔙 + 1)) (rC sources gamma hg hh p * (𝔙 + 1)) (𝔙 + 1) (U0 𝔏 𝔮) (ℌ) (𝔄) hL
    have hC : Rest.InvC (eSite selector xtra mask packets rows sources gamma hg hh p) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT ℜ (InitS.Rk ℜ)
        (KcW selector xtra mask packets rows sources gamma hg hh p mode) (K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci) (fun _ => 0)
        (Fin.last _) 𝔟 𝔮 (Mb 𝔏 𝔮) (InitPost.Ms 𝔏 𝔮) ℜ ℜ ℜ ℜ
        (sC sources gamma hg hh p * (𝔙 + 1)) (rC sources gamma hg hh p * (𝔙 + 1)) (𝔙 + 1) 𝔟 (U0 𝔏 𝔮) (ℌ) (𝔄) := by
      have h : Rest.InvC (eSite selector xtra mask packets rows sources gamma hg hh p) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT ℜ (InitS.Rk ℜ)
          (KcW selector xtra mask packets rows sources gamma hg hh p mode) (K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci) (fun _ => 0)
          (Fin.last _) 𝔟 (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒).arity (Mb 𝔏 𝔮) (InitPost.Ms 𝔏 𝔮) ℜ ℜ ℜ ℜ
          (sC sources gamma hg hh p * (𝔙 + 1)) (rC sources gamma hg hh p * (𝔙 + 1)) (𝔙 + 1) 𝔟 (U0 𝔏 𝔮) (ℌ) (𝔄) := hL.2.2.1
      rw [hA] at h
      exact h
    obtain ⟨w, hw, hw5⟩ := (henc hfirst).2.2.2
    refine ⟨ℌ, 𝔄, hrun.enlarge (by omega), hC, hL.2.2.2, hQ, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, henc hfirst, ?_⟩
    have hw5' : SourceSteps.queriedAt sources p den hden 𝔨 𝔯 𝔰 n x bits hp ci A (wholeW selector xtra mask packets rows sources gamma hg hh p
        (Dims.encT (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT 5)) = ZeroPadding.pad ℜ w := hw5
    have e1 : A (wholeW selector xtra mask packets rows sources gamma hg hh p
        (Dims.encT (d := 𝔡) (plSite selector xtra mask packets rows sources gamma hg hh p mode ph).hT 5)) = ZeroPadding.pad ℜ w :=
      hq5.symm.trans hw5'
    have hw' : w.length ≤ InitRun.D0 𝔟 := hw
    rw [e1, pad_take_pad ℜ (InitRun.D0 𝔟) w hw']
    exact hw5'

end site

end
end NearCubicWires.SourceSkeleton.StartA
end

