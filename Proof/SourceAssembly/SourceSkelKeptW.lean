import Proof.SourceAssembly.SourceRestIn4
import Proof.SourceAssembly.SourceSkelFirstW
import Proof.SourceAssembly.SourceStepsCode

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
namespace NearCubicWires.SourceSkeleton.KeptW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsR (gWR)
open NearCubicWires.SourceSkeleton.ParamsV4 (LW fPW sfPW)
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
noncomputable section

section kept
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇𝔰" => DSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔢" => eSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔬" => PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "ℭ" => PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)

def KSite (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) : Fin V → Prop :=
  Rest.srcK4 (d := 𝔡) (eX := (𝔇𝔰).se.extra) (pX := (𝔇𝔰).sp.extra) (gW := (𝔇𝔰).gW)
    (cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode)
    (terminalSite selector xtra mask packets rows sources gamma hg hh p V hV)

/-- The site's layout numbers. -/
theorem site_nums :
    (𝔡).F = 𝔬 + 1155 ∧ 301 ≤ 𝔬 ∧ (𝔡).F + (𝔡).rt + 13 ≤ (𝔡).B ∧ (𝔡).U = (𝔡).B + (𝔡).res ∧
      (𝔡).res = 39 + restPc (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW +
        (xROf (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p +
          NearCubicWires.SourceStart.MetaStepGF.wMG selector sources p packets (LW selector mask packets rows sources gamma hg hh p)) ∧
      25 ≤ xROf (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p := by
  refine ⟨rfl, PCJda54a286946142d3_BranchPhases.offset_ge _ _ _ _, ?_, ?_, rfl, ?_⟩
  · simp only [Dims.B, Dims.G]; omega
  · simp only [Dims.U, Dims.B, Dims.G, Dims.prepT]; omega
  · unfold xROf; omega

/-- The cache tapes lie below `F` (`< 2` or in `[302, offset)`). -/
theorem cache_nums (mode : Bool) (i : Fin 19) :
    (ℭ mode i).val < 2 ∨ (302 ≤ (ℭ mode i).val ∧ (ℭ mode i).val < 𝔬) :=
  SourcePhase.cache_range sources p _ _ _ mode i

/-- **`hKpos`** (S's `srcK4_pos`). -/
theorem KSite_pos (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (x : Fin V)
    (hx : KSite selector xtra mask packets rows sources gamma hg hh p V hV mode x) :
    x.val < (𝔡).F ∨ ((𝔡).B + 29 + restPc (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW ≤ x.val ∧
      x ≠ Dims.hrT 𝔢 hV 10 ∧ x ≠ Dims.hrT 𝔢 hV 11) := by
  obtain ⟨hF, ho, -, -, -, -⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  refine Rest.srcK4_pos 𝔢 hV _ _ (fun i => ?_) ?_ x hx
  · rw [cacheSite_val]; have := cache_nums selector xtra mask packets rows sources gamma hg hh p mode i; omega
  · show 𝔬 + 53 < (𝔡).F; omega

/-- Every kept tape lies below `U` (so it is never the loop counter `Fin.last U`: `hKcnt`). -/
theorem KSite_lt_U (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (x : Fin V)
    (hx : KSite selector xtra mask packets rows sources gamma hg hh p V hV mode x) : x.val < (𝔡).U := by
  obtain ⟨hF, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  rcases hx with h | h | h | h | h | h
  · rcases h with h | h | ⟨i, hi⟩ | h
    · omega
    · omega
    · rw [← hi, cacheSite_val]; have := cache_nums selector xtra mask packets rows sources gamma hg hh p mode i; omega
    · unfold Dims.HiRes at h; omega
  · omega
  · omega
  · omega
  · omega
  · rw [h]; show 𝔬 + 53 < _; omega

/-- **`hKcnt`** at the first universe (`cnt = Fin.last U`). -/
theorem KSite_cnt (mode : Bool) (x : Fin ((𝔡).U + 1))
    (hx : KSite selector xtra mask packets rows sources gamma hg hh p ((𝔡).U + 1) (Nat.le_succ _) mode x) :
    x ≠ Fin.last _ := by
  intro h
  have := KSite_lt_U selector xtra mask packets rows sources gamma hg hh p _ _ mode x hx
  rw [h] at this
  simp at this

/-- **`hKfree`**: every kept tape is free of the cycle's slot maps, or one of the rewind pair. -/
theorem KSite_free (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (x : Fin V)
    (hx : KSite selector xtra mask packets rows sources gamma hg hh p V hV mode x) :
    Cycle.Free ((𝔡).slot hV) ((𝔡).maskSlots hV) ((𝔡).pslots hV) ((𝔡).poolSlots hV) ((𝔡).familySlots hV)
        (Dims.rewind2Slots (𝔢).ext2.ext1.ext hV) x ∨
      x = Dims.rewind2Slots (𝔢).ext2.ext1.ext hV 1 ∨ x = Dims.rewind2Slots (𝔢).ext2.ext1.ext hV 2 := by
  obtain ⟨hF, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  have fb : ∀ y : Fin V, y.val ≠ 278 → y.val ≠ 279 → y.val < (𝔡).F →
      Cycle.Free ((𝔡).slot hV) ((𝔡).maskSlots hV) ((𝔡).pslots hV) ((𝔡).poolSlots hV) ((𝔡).familySlots hV)
        (Dims.rewind2Slots (𝔢).ext2.ext1.ext hV) y :=
    fun y a b c => SourceSteps.free_below (𝔢).ext2.ext1.ext hV y a b c
  have fr : ∀ y : Fin V, (𝔡).B ≤ y.val →
      Cycle.Free ((𝔡).slot hV) ((𝔡).maskSlots hV) ((𝔡).pslots hV) ((𝔡).poolSlots hV) ((𝔡).familySlots hV)
        (Dims.rewind2Slots (𝔢).ext2.ext1.ext hV) y :=
    fun y a => Dims.free_res (𝔢).ext2.ext1.ext hV y a
  rcases hx with h | h | h | h | h | h
  · rcases h with h | h | ⟨i, hi⟩ | h
    · exact Or.inl (fb x (by omega) (by omega) (by omega))
    · exact Or.inl (fb x (by omega) (by omega) (by omega))
    · have hc := cache_nums selector xtra mask packets rows sources gamma hg hh p mode i
      rw [← hi]
      exact Or.inl (fb _ (by rw [cacheSite_val]; omega) (by rw [cacheSite_val]; omega) (by rw [cacheSite_val]; omega))
    · unfold Dims.HiRes at h; exact Or.inl (fr x (by omega))
  · exact Or.inr (Or.inl (Fin.ext (by rw [h]; rfl)))
  · exact Or.inr (Or.inr (Fin.ext (by rw [h]; rfl)))
  · exact Or.inl (fr x (by omega))
  · exact Or.inl (fr x (by omega))
  · rw [h]; exact Or.inl (fb _ (by show 𝔬 + 53 ≠ 278; omega) (by show 𝔬 + 53 ≠ 279; omega) (by show 𝔬 + 53 < _; omega))

/-- A phase word slot's value at the site. -/
def wdS (ph : Phase) (i : Fin 278) : ℕ :=
  (SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph i).val

theorem wdS_val (ph : Phase) (i : Fin 278) (h4 : i.val ≠ 274) (h5 : i.val ≠ 275) :
    wdS selector xtra mask packets rows sources gamma hg hh p ph i = i.val ∨
      wdS selector xtra mask packets rows sources gamma hg hh p ph i = 𝔬 + 599 + ((C10TailUniformSlots.phaseIndex ph).val - 1) * 278 + i.val :=
  SourceSteps.wd_val mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p
    (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i h4 h5

theorem wdS_lt (ph : Phase) (i : Fin 278) : wdS selector xtra mask packets rows sources gamma hg hh p ph i < 𝔬 + 1155 :=
  wordSlot_lt sources p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph i

theorem wdS_not_cache (ph : Phase) (mode : Bool) (i : Fin 278) (h2 : 2 ≤ i.val) (j : Fin 19) :
    wdS selector xtra mask packets rows sources gamma hg hh p ph i ≠ (ℭ mode j).val := fun e =>
  SourcePhase.not_cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) mode
    (SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph i)
    (SourcePhase.wd_ge_two (sources := sources) (p := p) (k := kSite selector xtra mask packets rows sources gamma hg hh p) (r := rSite selector xtra mask packets rows sources gamma hg hh p)
      (scratch := scrSite selector mask packets rows sources gamma hg hh p) ph i h2)
    (SourcePhase.wordSlots_region _ _ _ _ ph i) j (Fin.ext e)

theorem wdS_ne_terminal (ph : Phase) (i : Fin 278) (h4 : i.val ≠ 274) (h5 : i.val ≠ 275) : wdS selector xtra mask packets rows sources gamma hg hh p ph i ≠ 𝔬 + 53 :=
  SourceSkeleton.wd_ne_terminal mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p
    (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i h4 h5

/-- The code's six `app` tapes by value: four above `F` (`F+rt+5`, `F+rt+10..12`) and the phase words `Wd ph 81/90`. -/
theorem app_cases (ph : Phase) (i : Fin 6) :
    appVal mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i =
      𝔬 + 1155 + r_tapes (printerOf sources) + 5 ∨
    appVal mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i =
      wdS selector xtra mask packets rows sources gamma hg hh p ph 81 ∨
    appVal mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i =
      𝔬 + 1155 + r_tapes (printerOf sources) + 10 ∨
    appVal mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i =
      wdS selector xtra mask packets rows sources gamma hg hh p ph 90 ∨
    appVal mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i =
      𝔬 + 1155 + r_tapes (printerOf sources) + 11 ∨
    appVal mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i =
      𝔬 + 1155 + r_tapes (printerOf sources) + 12 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- A kept tape is either below `F` and off the phase words `Wd ph 81/90`, or a high resident. -/
theorem kept_split (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (ph : Phase) (x : Fin V)
    (hx : KSite selector xtra mask packets rows sources gamma hg hh p V hV mode x) :
    (x.val < (𝔡).F ∧ x.val ≠ wdS selector xtra mask packets rows sources gamma hg hh p ph 81 ∧ x.val ≠ wdS selector xtra mask packets rows sources gamma hg hh p ph 90) ∨
      (𝔡).B + 29 + restPc (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW ≤ x.val := by
  obtain ⟨hF, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  have w81 := wdS_val selector xtra mask packets rows sources gamma hg hh p ph 81 (by decide) (by decide)
  have w90 := wdS_val selector xtra mask packets rows sources gamma hg hh p ph 90 (by decide) (by decide)
  have hp := (C10TailUniformSlots.phaseIndex ph).isLt
  rcases hx with h | h | h | h | h | h
  · rcases h with h | h | ⟨j, hj⟩ | h
    · left; exact ⟨by omega, by omega, by omega⟩
    · left; exact ⟨by omega, by omega, by omega⟩
    · have hc := cache_nums selector xtra mask packets rows sources gamma hg hh p mode j
      have n81 := wdS_not_cache selector xtra mask packets rows sources gamma hg hh p ph mode 81 (by decide) j
      have n90 := wdS_not_cache selector xtra mask packets rows sources gamma hg hh p ph mode 90 (by decide) j
      left
      rw [← hj, cacheSite_val]
      exact ⟨by omega, fun e => n81 e.symm, fun e => n90 e.symm⟩
    · unfold Dims.HiRes at h; right; omega
  · left; exact ⟨by omega, by omega, by omega⟩
  · left; exact ⟨by omega, by omega, by omega⟩
  · right; omega
  · right; omega
  · have t81 := wdS_ne_terminal selector xtra mask packets rows sources gamma hg hh p ph 81 (by decide) (by decide)
    have t90 := wdS_ne_terminal selector xtra mask packets rows sources gamma hg hh p ph 90 (by decide) (by decide)
    left
    rw [h]
    change 𝔬 + 53 < _ ∧ 𝔬 + 53 ≠ _ ∧ 𝔬 + 53 ≠ _
    exact ⟨by omega, fun e => t81 e.symm, fun e => t90 e.symm⟩

/-- **`hKapp`**: the code's `app` tapes are never kept. -/
theorem KSite_app (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (ph : Phase) (x : Fin V)
    (hx : KSite selector xtra mask packets rows sources gamma hg hh p V hV mode x) (i : Fin 6) :
    appVal mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) ph i ≠
      x.val := by
  obtain ⟨hF, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  have l81 := wdS_lt selector xtra mask packets rows sources gamma hg hh p ph 81
  have l90 := wdS_lt selector xtra mask packets rows sources gamma hg hh p ph 90
  have hrtd : (𝔡).rt = r_tapes (printerOf sources) := rfl
  have hk := kept_split selector xtra mask packets rows sources gamma hg hh p V hV mode ph x hx
  intro he
  rcases app_cases selector xtra mask packets rows sources gamma hg hh p ph i with h | h | h | h | h | h <;> rw [h] at he <;> omega

/-! ## The kept words -/

def K0Site (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) (x : Fin V) : List Bool :=
  if h : ∃ i, cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode i = x then cdW (Classical.choose h)
  else if x.val = 1 then frameW
  else if x.val = 284 then qW
  else if x.val = 278 then List.replicate Vv true
  else if x.val = 279 then List.replicate Vv false
  else if x = terminalSite selector xtra mask packets rows sources gamma hg hh p V hV then List.replicate NC true
  else resW (x.val - ((𝔡).B + 29 + restPc (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW))

theorem K0Site_cache (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) (i : Fin 19) :
    K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC
      (cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode i) = cdW i := by
  have hex : ∃ j, cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode j =
      cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode i := ⟨i, rfl⟩
  have inj := PCJ30aa6f1b7c2a4221_.Selected.cache_injective sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
    (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) mode
  unfold K0Site
  rw [dif_pos hex]
  congr 1
  have hc := Classical.choose_spec hex
  have hv := congrArg Fin.val hc
  rw [cacheSite_val, cacheSite_val] at hv
  exact inj (Fin.ext hv)

/-- A non-cache tape's kept word. -/
theorem K0Site_off (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) (x : Fin V) (hx : ∀ i, (ℭ mode i).val ≠ x.val) :
    K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC x =
      if x.val = 1 then frameW
      else if x.val = 284 then qW
      else if x.val = 278 then List.replicate Vv true
      else if x.val = 279 then List.replicate Vv false
      else if x = terminalSite selector xtra mask packets rows sources gamma hg hh p V hV then List.replicate NC true
      else resW (x.val - ((𝔡).B + 29 + restPc (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW)) := by
  have hn : ¬ ∃ i, cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode i = x := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    rw [cacheSite_val] at hv
    exact hx i hv
  unfold K0Site
  rw [dif_neg hn]

/-- **`hKr1`/`hKr2`** (the rewind words, at `dR = Vv`). -/
theorem K0Site_rew (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) :
    K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC
        (Dims.rewind2Slots (𝔢).ext2.ext1.ext hV 1) = List.replicate Vv true ∧
      K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC
        (Dims.rewind2Slots (𝔢).ext2.ext1.ext hV 2) = List.replicate Vv false := by
  have hc : ∀ (y : Fin V), (y.val = 278 ∨ y.val = 279) → ∀ i, (ℭ mode i).val ≠ y.val := by
    intro y hy i
    have := cache_nums selector xtra mask packets rows sources gamma hg hh p mode i
    omega
  have v1 : (Dims.rewind2Slots (𝔢).ext2.ext1.ext hV 1).val = 278 := rfl
  have v2 : (Dims.rewind2Slots (𝔢).ext2.ext1.ext hV 2).val = 279 := rfl
  constructor
  · rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC _ (hc _ (Or.inl v1))]
    simp [v1]
  · rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC _ (hc _ (Or.inr v2))]
    simp [v2]

/-- **`hK284`**: the query copy's kept word is `qW`. -/
theorem K0Site_284 (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) :
    K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC
      (q284Site selector xtra mask packets rows sources gamma hg hh p V hV) = qW := by
  have hv : (q284Site selector xtra mask packets rows sources gamma hg hh p V hV).val = 284 := rfl
  rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC _ (fun i => by
    have := cache_nums selector xtra mask packets rows sources gamma hg hh p mode i; rw [hv]; omega)]
  simp [hv]

/-- **`hKpad`**: every kept tape at or above `F` is a strip resident, whose word is padded to `Rc` once every `resW i` is `Rc`-long. -/
theorem K0Site_pad (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC Rc : ℕ) (hres : ∀ i, Rc ≤ (resW i).length) (x : Fin V)
    (hx : KSite selector xtra mask packets rows sources gamma hg hh p V hV mode x) (hxF : (𝔡).F ≤ x.val) :
    ZeroPadding.pad Rc (K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC x) =
      K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC x := by
  obtain ⟨hF, ho, hB, hU, hres', hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  have hc : ∀ i, (ℭ mode i).val ≠ x.val := fun i => by
    have := cache_nums selector xtra mask packets rows sources gamma hg hh p mode i; omega
  have ht : x ≠ terminalSite selector xtra mask packets rows sources gamma hg hh p V hV := fun h => by
    have hv := congrArg Fin.val h; change x.val = 𝔬 + 53 at hv; omega
  rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC x hc]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg ht]
  have hl := hres (x.val - ((𝔡).B + 29 + restPc (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW))
  simp [ZeroPadding.pad, Nat.sub_eq_zero_of_le hl]

end kept

end
end NearCubicWires.SourceSkeleton.KeptW
end

