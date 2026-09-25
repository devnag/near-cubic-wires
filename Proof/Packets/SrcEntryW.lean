import Proof.SourceAssembly.SourceSkelStartGuard
import Proof.Packets.SrcPen0

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
namespace NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.KeptW
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
local notation "𝔇𝔰" => DSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔬" => PCJda54a286946142d3_BranchPhases.offset sources p
  (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p)
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
local notation "ℭ" => PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "𝔅𝔗" => ControllerSelectedContinuation.bodyTapes sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "ℭ𝔖" => cacheSite selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)

/-- The site universe `U + 1` IS the body's tape count. -/
theorem U_succ_eq : 𝔘 + 1 = 𝔅𝔗 :=
  dims_U mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p 𝔨 𝔯

/-- **`whole`**: the site tape `i` as the body tape `i`. -/
def wholeW : Fin (𝔘 + 1) → Fin 𝔅𝔗 := fun i =>
  ⟨i.val, lt_of_lt_of_eq i.isLt (U_succ_eq selector xtra mask packets rows sources gamma hg hh p)⟩

def KcW (mode : Bool) (y : Fin (𝔘 + 1)) : Prop :=
  KSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode y ∧ y ≠ ℭ𝔖 mode 15 ∧
    y ≠ q284Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _)

/-- **The K0Site wrapper**: the kept words at clause `ci` (cache = `cdAt ci`, query copy = `pad capC (qwordAt ci)`, tape `1` = `frame bits`,
terminal = `1^NC`, the init's strip words, `Vv = VvOf`; StartGuard's `K0S` at any onset). -/
def K0W (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) : Phase → ℕ → Fin (𝔘 + 1) → List Bool := fun _ ci =>
  K0Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode (RepairOrdinary.frame bits)
    (ZeroPadding.pad (capC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) (SourceSteps.qwordAt sources p 𝔨 n x bits ci))
    (SourceSteps.cdAt sources p 𝔨 n x bits ci)
    (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n (C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n)) 𝔙
    (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒)

def EW (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) : SourceSteps.EntrySite 𝔅𝔗 where
  d := 𝔡
  eX := (𝔇𝔰).se.extra
  pX := (𝔇𝔰).sp.extra
  gW := (𝔇𝔰).gW
  eR := hRx4 selector mask packets rows sources gamma hg hh p
  eV := SourceBudget.Params.hVN selector sources gamma hg hh p
  X := initX (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p
  T := 𝔘 + 1
  whole := wholeW selector xtra mask packets rows sources gamma hg hh p
  pl := fun ph => plSite selector xtra mask packets rows sources gamma hg hh p mode ph
  e := eSite selector xtra mask packets rows sources gamma hg hh p
  Rc := ℜ
  Rk := InitS.Rk ℜ
  Ce := WorkspaceSelectedEntryBudget.envelope sources p 𝔨 𝔯 n + 1
  Kc := KcW selector xtra mask packets rows sources gamma hg hh p mode
  K0 := K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits
  KH0 := fun _ => 0
  cnt := Fin.last _
  c15 := ℭ𝔖 mode 15
  q284 := q284Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _)
  c17 := ℭ𝔖 mode 17
  c18 := ℭ𝔖 mode 18
  b := C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n
  q := (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒).arity
  Mb := NearCubicWires.SourceConstruction.InitRun.Mb 𝔏 𝔮
  Ms := NearCubicWires.SourceConstruction.InitPost.Ms 𝔏 𝔮
  S := sC sources gamma hg hh p * (𝔙 + 1)
  Rw := rC sources gamma hg hh p * (𝔙 + 1)
  B := 𝔙 + 1
  U0 := NearCubicWires.SourceConstruction.InitRun.U0 𝔏 𝔮

/-- `EW`'s kept words, unfolded. -/
theorem ew_K0_eq (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) (ci : ℕ) (y : Fin (𝔘 + 1)) :
    (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).K0 ph ci y =
      K0Site selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) mode (RepairOrdinary.frame bits)
        (ZeroPadding.pad (capC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) (SourceSteps.qwordAt sources p 𝔨 n x bits ci))
        (SourceSteps.cdAt sources p 𝔨 n x bits ci)
        (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n (C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n)) 𝔙
        (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) y := by
  dsimp only [EW, K0W]

/-! ## The bridge's ten layout facts -/

theorem ew_whole (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    ∀ i, ((EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole i).val = i.val := fun _ => rfl

theorem ew_Fo (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    𝔬 + 1155 ≤ (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).d.F :=
  le_of_eq (site_nums selector xtra mask packets rows sources gamma hg hh p).1.symm

theorem ew_cnt (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).d.F ≤ (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).cnt.val := by
  show (𝔡).F ≤ (Fin.last 𝔘).val
  rw [Fin.val_last]
  exact F_le_USite selector xtra mask packets rows sources gamma hg hh p

/-- **`hKlow`**: a kept tape below `F` is a cache tape, tape `1`, or in `[278, offset + 124)` (the rewind pair, the terminal `offset + 53`). -/
theorem ew_Klow (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    ∀ y, (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).Kc y → y.val < (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).d.F →
      (∃ i, (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole y = ℭ mode i) ∨ y.val < 2 ∨ (278 ≤ y.val ∧ y.val < 𝔬 + 124) := by
  intro (y : Fin (𝔘 + 1)) hy hF
  change KcW selector xtra mask packets rows sources gamma hg hh p mode y at hy
  change y.val < (𝔡).F at hF
  obtain ⟨hk, -, hq⟩ := hy
  obtain ⟨hFn, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  rcases hk with h | h | h | h | h | h
  · rcases h with h | h | ⟨j, hj⟩ | h
    · right; left; omega
    · exact absurd (Fin.ext (by rw [h]; rfl)) hq
    · left
      subst hj
      exact ⟨j, Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits _).trans
        (cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode j))⟩
    · unfold Dims.HiRes at h; omega
  · right; right; omega
  · right; right; omega
  · omega
  · omega
  · right; right
    have hv : y.val = 𝔬 + 53 := by rw [h]; rfl
    omega

/-- **`hK0`**: off the cache, a kept tape's word does not depend on the clause (the query copy `284` is not kept). -/
theorem ew_K0 (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    ∀ ph ph' : Phase, (ph = .penalty ∧ ph' = .moment) ∨ (ph = .moment ∧ ph' = .clause) →
      ∀ y, (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).Kc y →
        (∀ i, (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole y ≠ ℭ mode i) →
        (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).K0 ph' 0 y =
          (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).K0 ph (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) y := by
  intro ph ph' _ (y : Fin (𝔘 + 1)) hy hc
  change KcW selector xtra mask packets rows sources gamma hg hh p mode y at hy
  have hc' : ∀ i, (ℭ mode i).val ≠ y.val := fun i h =>
    hc i (Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits y).trans h.symm))
  have h284 : y.val ≠ 284 := fun h => hy.2.2 (Fin.ext (by rw [h]; rfl))
  rw [ew_K0_eq, ew_K0_eq, K0Site_off selector xtra mask packets rows sources gamma hg hh p _ _ mode _ _ _ _ _ _ y hc',
    K0Site_off selector xtra mask packets rows sources gamma hg hh p _ _ mode _ _ _ _ _ _ y hc', if_neg h284, if_neg h284]

/-- **`hK0c`**: a kept cache tape holds clause `ci`'s `cdAt`. -/
theorem ew_K0c (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    ∀ (ph : Phase) (ci : Nat) y i, (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).Kc y →
      (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole y = ℭ mode i →
      (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).K0 ph ci y = SourceSteps.cdAt sources p 𝔨 n x bits ci i := by
  intro ph ci (y : Fin (𝔘 + 1)) i _ hw
  have hy : y = ℭ𝔖 mode i :=
    Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits y).symm.trans
      ((congrArg Fin.val hw).trans (cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode i).symm))
  subst hy
  exact (ew_K0_eq selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci _).trans
    (K0Site_cache selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode _ _ _ _ _ _ i)

theorem ew_15 (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).c15 = ℭ mode 15 :=
  Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits _).trans
    (cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 15))

theorem ew_17 (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).c17 = ℭ mode 17 :=
  Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits _).trans
    (cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 17))

theorem ew_18 (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).c18 = ℭ mode 18 :=
  Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits _).trans
    (cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 18))

theorem ew_284 (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).q284.val = 284 := rfl

set_option hygiene false in
local notation "𝔪" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) n x bits hp
set_option hygiene false in
local notation "ℕℭ" => NC sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) x
  (C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
    (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits)

theorem ew_bridge (den : ℕ) (hden : 0 < den) (n : ℕ) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (EF : Phase → Fin ℕℭ → List CloseoutRowsEstimatorCoefficients.Stream.Entry) :
    ∀ (ph ph' : Phase), (ph = .penalty ∧ ph' = .moment) ∨ (ph = .moment ∧ ph' = .clause) →
    ∀ (A : Fin 𝔅𝔗 → List Bool) (H : Fin 𝔅𝔗 → Nat)
      (A' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p 𝔨 𝔯 𝔰) → List Bool) (H' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p 𝔨 𝔯 𝔰) → Nat),
      SourceSteps.entryInvAt3 sources p den hden 𝔨 𝔯 𝔰 n x bits hp (EW selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) EF ph ℕℭ A H →
      (∀ t, (∀ j, Wd sources p 𝔨 𝔯 𝔰 ph j ≠ t) → (∀ j, Fd sources p 𝔨 𝔯 𝔰 ph j ≠ t) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p 𝔨 𝔯 𝔰 t) = A t) →
      (∀ t, H' (PCJda54a286946142d3_BranchPhases.body sources p 𝔨 𝔯 𝔰 t) = H t) →
      (∀ i : Fin 218, (i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p 𝔨 𝔯 𝔰 (Fd sources p 𝔨 𝔯 𝔰 ph (i.castAdd 1))) =
          A (Fd sources p 𝔨 𝔯 𝔰 ph (i.castAdd 1))) →
      SourceSteps.entryInvAt3 sources p den hden 𝔨 𝔯 𝔰 n x bits hp (EW selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) EF ph' 0
        (laterA0 sources p 𝔨 𝔯 𝔰 (PolynomialClock.ordinaryClock 𝔨) x 𝔒 𝔪 A')
        (fun i => H' (PCJda54a286946142d3_BranchPhases.body sources p 𝔨 𝔯 𝔰 i)) :=
  SourceSteps.bridge_entryInvAt3 sources p den hden 𝔨 𝔯 𝔰 n x bits hp (EW selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) EF
    (ew_whole selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) (ew_Fo selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits)
    (ew_cnt selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) (ew_Klow selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits)
    (ew_K0 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) (ew_K0c selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits)
    (ew_15 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) (ew_17 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits)
    (ew_18 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) (ew_284 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits)

/-! ## `pen0` at `EW` -/

theorem ew_ar (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole ((EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).pl .penalty).ar = ℭ mode 13 :=
  Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits _).trans
    (cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 13))

theorem ew_wd (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole ((EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).pl .penalty).wd =
      Wd sources p 𝔨 𝔯 𝔰 .penalty 218 := by
  apply Fin.ext
  rw [ew_whole]
  have lt : (Wd sources p 𝔨 𝔯 𝔰 .penalty 218).val < 𝔘 + 1 :=
    lt_of_lt_of_eq (Wd sources p 𝔨 𝔯 𝔰 .penalty 218).isLt (U_succ_eq selector xtra mask packets rows sources gamma hg hh p).symm
  have e : ((EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).pl .penalty).wd = (⟨(Wd sources p 𝔨 𝔯 𝔰 .penalty 218).val, lt⟩ : Fin (𝔘 + 1)) := rfl
  rw [e, Fin.val_mk]

/-- **`hKpen`**: a kept tape below `F` off `278..284` is a cache tape (clause `0`'s `cdAt`), tape `1` (`frame bits`) or the terminal (`1^NC`); heads `0`. -/
theorem ew_Kpen (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) :
    ∀ y, (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).Kc y → y.val < (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).d.F →
      (y.val < 278 ∨ 285 ≤ y.val) → (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).KH0 y = 0 ∧
      ((∃ i, (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole y = ℭ mode i ∧
          (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).K0 .penalty 0 y = SourceSteps.cdAt sources p 𝔨 n x bits 0 i) ∨
       (y.val = 1 ∧ (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).K0 .penalty 0 y = RepairOrdinary.frame bits) ∨
       ((EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).whole y = PCJ30aa6f1b7c2a4221_.Selected.terminal sources p 𝔨 𝔯 𝔰 ∧
          (EW selector xtra mask packets rows sources gamma hg hh p mode n x bits).K0 .penalty 0 y = List.replicate (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) true)) := by
  intro (y : Fin (𝔘 + 1)) hy hF hr
  refine ⟨rfl, ?_⟩
  change KcW selector xtra mask packets rows sources gamma hg hh p mode y at hy
  change y.val < (𝔡).F at hF
  obtain ⟨hk, -, hq⟩ := hy
  obtain ⟨hFn, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  by_cases hc : ∃ i, ℭ𝔖 mode i = y
  · obtain ⟨i, hi⟩ := hc
    subst hi
    left
    exact ⟨i, Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits _).trans
        (cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode i)),
      (ew_K0_eq selector xtra mask packets rows sources gamma hg hh p mode n x bits .penalty 0 _).trans
        (K0Site_cache selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode _ _ _ _ _ _ i)⟩
  · have hc' : ∀ i, (ℭ mode i).val ≠ y.val := fun i h =>
      hc ⟨i, Fin.ext ((cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode i).trans h)⟩
    rcases hk with h | h | h | h | h | h
    · rcases h with h | h | ⟨j, hj⟩ | h
      · right; left
        refine ⟨h, ?_⟩
        rw [ew_K0_eq, K0Site_off selector xtra mask packets rows sources gamma hg hh p _ _ mode _ _ _ _ _ _ y hc', if_pos h]
      · exact absurd (Fin.ext (by rw [h]; rfl)) hq
      · exact absurd ⟨j, hj⟩ hc
      · unfold Dims.HiRes at h; omega
    · omega
    · omega
    · omega
    · omega
    · subst h
      right; right
      refine ⟨Fin.ext ((ew_whole selector xtra mask packets rows sources gamma hg hh p mode n x bits _).trans
          ((show (terminalSite selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _)).val = 𝔬 + 53 from rfl).trans
            (term_val sources p 𝔨 𝔯 𝔰).symm)),
        (ew_K0_eq selector xtra mask packets rows sources gamma hg hh p mode n x bits .penalty 0 _).trans
          (K0Site_terminal selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode _ _ _ _ _ _)⟩

theorem ew_pen0Facts (den : ℕ) (hden : 0 < den) (n : ℕ) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) :
    NearCubicWires.SourceStart.Pen0.Pen0Facts sources p den hden 𝔨 𝔯 𝔰 n x bits hp (EW selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) where
  hwhole := ew_whole selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  hFo := ew_Fo selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  hcnt := ew_cnt selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  har := ew_ar selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  hq := rfl
  hwd := ew_wd selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  hb := rfl
  hCe := le_rfl
  h15 := ew_15 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  h17 := ew_17 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  h18 := ew_18 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  h284 := ew_284 selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits
  hKpen := ew_Kpen selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits

/-- **C3 at `EW`**: the clause-entry invariant at the penalty entry, for every phase-entry family `EF`. -/
theorem ew_pen0 (den : ℕ) (hden : 0 < den) (n : ℕ) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (EF : Phase → Fin ℕℭ → List CloseoutRowsEstimatorCoefficients.Stream.Entry) :
    SourceSteps.Pen0Hole sources p den hden 𝔨 𝔯 𝔰 n x bits hp (EW selector xtra mask packets rows sources gamma hg hh p 𝔪 n x bits) EF :=
  NearCubicWires.SourceStart.Pen0.pen0_generic sources p den hden 𝔨 𝔯 𝔰 n x bits hp _ EF
    (ew_pen0Facts selector xtra mask packets rows sources gamma hg hh p den hden n x bits hp)

end site

end
end NearCubicWires.SourceStart.EntryW
end

