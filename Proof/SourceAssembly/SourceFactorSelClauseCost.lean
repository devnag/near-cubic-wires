import Proof.SourceAssembly.SourceStepsNums
import Proof.SourceAssembly.SourceStepsParamsV4

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceBudget NearCubicWires.SourceSkeleton.ClassR
open NearCubicWires.SourceConstruction NearCubicWires.SourceBudget.Params
namespace NearCubicWires.SourceFactorSel.ClauseCost
noncomputable section

theorem table_raise (L h q : ℕ) : RuntimeShape.tableClass L 0 q ≤ RuntimeShape.tableClass L h q := by
  unfold RuntimeShape.tableClass
  exact Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ (by omega))

/-- A quantity below `tableClass L 0 q` is a unit TABLE coefficient at any exponents. -/
theorem g_in {dP hT hS m L n qn g : ℕ} (hg : g ≤ RuntimeShape.tableClass L 0 qn) :
    Admission.InClasses dP hT hS m L n qn 0 1 0 g :=
  Admission.InClasses.table (by have := table_raise L hT qn; omega)

section generic
variable (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) (y yF0 I : ClsFam)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (capIndex : ParNat)

set_option hygiene false in
local notation "𝔅" => siteBIR printer cVc hV y yF0 I
set_option hygiene false in
local notation "ℜ" => siteRcR printer cVc hV y yF0
set_option hygiene false in
local notation "𝔏" => liveOfR (siteBIR printer cVc hV y yF0 I).hT sources gamma hg hh p
set_option hygiene false in
local notation "𝔨" => kSelR (baseR (siteBIR printer cVc hV y yF0 I)).ofBaseR capIndex sources gamma hg hh p

def zRef : CostCls :=
  ⟨y.dP sources gamma hg hh p, y.hT sources gamma hg hh p, y.hS sources gamma hg hh p 𝔏,
    y.cP sources gamma hg hh p 𝔨 + 0, y.cT sources gamma hg hh p 𝔨 + 1, y.cS sources gamma hg hh p 𝔨 + 0⟩

def zFirst : CostCls :=
  ⟨yF0.dP sources gamma hg hh p, yF0.hT sources gamma hg hh p, yF0.hS sources gamma hg hh p 𝔏,
    yF0.cP sources gamma hg hh p 𝔨 + 0 + 1, yF0.cT sources gamma hg hh p 𝔨 + 1, yF0.cS sources gamma hg hh p 𝔨 + 0⟩

theorem zRef_ex : ∃ n0, ∀ n, n0 ≤ n → ∀ free : ℕ,
    (zRef printer cVc hV y yF0 I sources gamma hg hh p capIndex).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) free →
      free + 2 ≤ (ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
        (C10PartsSchedule.widthAt sources 𝔨 n) :=
  windows_siteBIR printer cVc hV y yF0 I sources gamma hg hh p capIndex _
    (y_dP_le_siteBIR printer cVc hV y yF0 I sources gamma hg hh p)
    (siteRcR_conds printer cVc hV y yF0 sources gamma hg hh p).2.2.1

theorem zFirst_ex : ∃ n0, ∀ n, n0 ≤ n → ∀ free : ℕ,
    (zFirst printer cVc hV y yF0 I sources gamma hg hh p capIndex).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) free →
      free + 2 ≤ (ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
        (C10PartsSchedule.widthAt sources 𝔨 n) :=
  windows_siteBIR printer cVc hV y yF0 I sources gamma hg hh p capIndex _
    (yF0_dP_le_siteBIR printer cVc hV y yF0 I sources gamma hg hh p)
    (siteRcR_conds printer cVc hV y yF0 sources gamma hg hh p).2.2.2.1

/-- **The refill windows' onset.** -/
def refOn : ℕ := Classical.choose (zRef_ex printer cVc hV y yF0 I sources gamma hg hh p capIndex)
/-- **The first cycle's windows' onset.** -/
def firstOn : ℕ := Classical.choose (zFirst_ex printer cVc hV y yF0 I sources gamma hg hh p capIndex)

theorem refill_window (n : ℕ) (hn : refOn printer cVc hV y yF0 I sources gamma hg hh p capIndex ≤ n) (x g : ℕ)
    (hy : (y.at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) x)
    (hg7 : g ≤ RuntimeShape.tableClass 𝔏 0 (C10PartsSchedule.widthAt sources 𝔨 n)) :
    x + g + 2 ≤ (ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
      (C10PartsSchedule.widthAt sources 𝔨 n) := by
  have hz : (zRef printer cVc hV y yF0 I sources gamma hg hh p capIndex).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) (x + g) :=
    Admission.InClasses.add hy (g_in hg7)
  exact Classical.choose_spec (zRef_ex printer cVc hV y yF0 I sources gamma hg hh p capIndex) n hn _ hz

theorem first_window (n : ℕ) (hn : firstOn printer cVc hV y yF0 I sources gamma hg hh p capIndex ≤ n) (x g : ℕ)
    (hy : (yF0.at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) x)
    (hg7 : g ≤ RuntimeShape.tableClass 𝔏 0 (C10PartsSchedule.widthAt sources 𝔨 n)) :
    x + g + 1 + 2 ≤ (ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
      (C10PartsSchedule.widthAt sources 𝔨 n) := by
  have hz : (zFirst printer cVc hV y yF0 I sources gamma hg hh p capIndex).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) (x + g + 1) :=
    Admission.InClasses.add_const 1 (Admission.InClasses.add hy (g_in hg7))
  exact Classical.choose_spec (zFirst_ex printer cVc hV y yF0 I sources gamma hg hh p capIndex) n hn _ hz

theorem g_in_ref (L k n qn g : ℕ) (hg7 : g ≤ RuntimeShape.tableClass L 0 qn) :
    ((refFam (ℜ) y).at sources gamma hg hh p L k).In 4 L n qn g := by
  have h0 : Admission.InClasses ((refFam (ℜ) y).at sources gamma hg hh p L k).dP ((refFam (ℜ) y).at sources gamma hg hh p L k).hT
      ((refFam (ℜ) y).at sources gamma hg hh p L k).hS 4 L n qn 0 1 0 g := g_in hg7
  have hc : 1 ≤ ((refFam (ℜ) y).at sources gamma hg hh p L k).cT := by
    show 1 ≤ 96 * 1 + y.cT sources gamma hg hh p k
    omega
  exact Admission.InClasses.coeff_mono (Nat.zero_le _) hc (Nat.zero_le _) h0

theorem g_in_first (L k n qn g : ℕ) (hg7 : g ≤ RuntimeShape.tableClass L 0 qn) :
    ((firstFam (ℜ) (yF0.join I)).at sources gamma hg hh p L k).In 4 L n qn g := by
  have h0 : Admission.InClasses ((firstFam (ℜ) (yF0.join I)).at sources gamma hg hh p L k).dP
      ((firstFam (ℜ) (yF0.join I)).at sources gamma hg hh p L k).hT
      ((firstFam (ℜ) (yF0.join I)).at sources gamma hg hh p L k).hS 4 L n qn 0 1 0 g := g_in hg7
  have hc : 1 ≤ ((firstFam (ℜ) (yF0.join I)).at sources gamma hg hh p L k).cT := by
    show 1 ≤ 102 * 1 + (yF0.join I).cT sources gamma hg hh p k
    omega
  exact Admission.InClasses.coeff_mono (Nat.zero_le _) hc (Nat.zero_le _) h0

/-- **The refill fuel's class**: `96·Rc + (x + g + 115)` is below `B`'s base RHS, for `x` in `y` and `g ≤ tableClass L 0 q`. -/
theorem refill_in_B (n Rc x g : ℕ)
    (hRc : Rc ≤ (ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
      (C10PartsSchedule.widthAt sources 𝔨 n))
    (hy : (y.at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) x)
    (hg7 : g ≤ RuntimeShape.tableClass 𝔏 0 (C10PartsSchedule.widthAt sources 𝔨 n)) :
    96 * Rc + (x + g + 115) ≤ Admission.splitRHS ((baseR 𝔅).dS sources gamma hg hh p) ((baseR 𝔅).hT sources gamma hg hh p)
      ((baseR 𝔅).hS sources gamma hg hh p) ((baseR 𝔅).m sources gamma hg hh p) ((baseR 𝔅).L sources gamma hg hh p)
      ((baseR 𝔅).cP sources gamma hg hh p 𝔨) ((baseR 𝔅).cT sources gamma hg hh p 𝔨) ((baseR 𝔅).cS sources gamma hg hh p 𝔨) n
      (C10PartsSchedule.widthAt sources 𝔨 n) := by
  have hz : 96 * Rc ≤ 96 * ((ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
      (C10PartsSchedule.widthAt sources 𝔨 n)) := Nat.mul_le_mul_left _ hRc
  have hy' : (⟨y.dP sources gamma hg hh p, y.hT sources gamma hg hh p, y.hS sources gamma hg hh p 𝔏,
      y.cP sources gamma hg hh p 𝔨 + 115, y.cT sources gamma hg hh p 𝔨, y.cS sources gamma hg hh p 𝔨⟩ : CostCls).In 4 𝔏 n
      (C10PartsSchedule.widthAt sources 𝔨 n) (x + 115) := Admission.InClasses.add_const 115 hy
  have hr : ((refFam (ℜ) y).at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) (96 * Rc + (x + 115)) :=
    refill_in_refCls 96 _ _ _ hz hy'
  have hrs : (((famSiteR printer cVc hV).at sources gamma hg hh p 𝔏 𝔨).join ((refFam (ℜ) y).at sources gamma hg hh p 𝔏 𝔨)).In 4 𝔏 n
      (C10PartsSchedule.widthAt sources 𝔨 n) (96 * Rc + (x + 115)) := hr.mono_cls (CostCls.le_join_right _ _)
  have hgf := g_in_first printer cVc hV y yF0 I sources gamma hg hh p 𝔏 𝔨 n _ g hg7
  have e : (𝔅).at sources gamma hg hh p 𝔏 𝔨 = (((famSiteR printer cVc hV).at sources gamma hg hh p 𝔏 𝔨).join
      ((refFam (ℜ) y).at sources gamma hg hh p 𝔏 𝔨)).join ((firstFam (ℜ) (yF0.join I)).at sources gamma hg hh p 𝔏 𝔨) := rfl
  have hB : ((𝔅).at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) (96 * Rc + (x + 115) + g) := by
    rw [e]
    exact CostCls.In.join_add hrs hgf
  have hle := base_splitRHSR 𝔅 sources gamma hg hh p 𝔨 n (C10PartsSchedule.widthAt sources 𝔨 n) _ hB
  have e2 : 96 * Rc + (x + g + 115) = 96 * Rc + (x + 115) + g := by omega
  rw [e2]
  exact hle

theorem first_in_B (n Rc icost x g : ℕ)
    (hRc : Rc ≤ (ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
      (C10PartsSchedule.widthAt sources 𝔨 n))
    (hI : (I.at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) icost)
    (hy : (yF0.at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) x)
    (hg7 : g ≤ RuntimeShape.tableClass 𝔏 0 (C10PartsSchedule.widthAt sources 𝔨 n)) :
    102 * Rc + (icost + x + g + 147) ≤ Admission.splitRHS ((baseR 𝔅).dS sources gamma hg hh p) ((baseR 𝔅).hT sources gamma hg hh p)
      ((baseR 𝔅).hS sources gamma hg hh p) ((baseR 𝔅).m sources gamma hg hh p) ((baseR 𝔅).L sources gamma hg hh p)
      ((baseR 𝔅).cP sources gamma hg hh p 𝔨) ((baseR 𝔅).cT sources gamma hg hh p 𝔨) ((baseR 𝔅).cS sources gamma hg hh p 𝔨) n
      (C10PartsSchedule.widthAt sources 𝔨 n) := by
  have hz : 102 * Rc ≤ 102 * ((ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
      (C10PartsSchedule.widthAt sources 𝔨 n)) := Nat.mul_le_mul_left _ hRc
  have hj : ((yF0.join I).at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) (x + icost) :=
    CostCls.In.join_add hy hI
  have hy' : (⟨(yF0.join I).dP sources gamma hg hh p, (yF0.join I).hT sources gamma hg hh p, (yF0.join I).hS sources gamma hg hh p 𝔏,
      (yF0.join I).cP sources gamma hg hh p 𝔨 + 147, (yF0.join I).cT sources gamma hg hh p 𝔨,
      (yF0.join I).cS sources gamma hg hh p 𝔨⟩ : CostCls).In 4 𝔏 n
      (C10PartsSchedule.widthAt sources 𝔨 n) (x + icost + 147) := Admission.InClasses.add_const 147 hj
  have hf : ((firstFam (ℜ) (yF0.join I)).at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n)
      (102 * Rc + (x + icost + 147)) := refill_in_refCls 102 _ _ _ hz hy'
  have hgr := g_in_ref printer cVc hV y yF0 sources gamma hg hh p 𝔏 𝔨 n _ g hg7
  have hgs : (((famSiteR printer cVc hV).at sources gamma hg hh p 𝔏 𝔨).join ((refFam (ℜ) y).at sources gamma hg hh p 𝔏 𝔨)).In 4 𝔏 n
      (C10PartsSchedule.widthAt sources 𝔨 n) g := hgr.mono_cls (CostCls.le_join_right _ _)
  have e : (𝔅).at sources gamma hg hh p 𝔏 𝔨 = (((famSiteR printer cVc hV).at sources gamma hg hh p 𝔏 𝔨).join
      ((refFam (ℜ) y).at sources gamma hg hh p 𝔏 𝔨)).join ((firstFam (ℜ) (yF0.join I)).at sources gamma hg hh p 𝔏 𝔨) := rfl
  have hB : ((𝔅).at sources gamma hg hh p 𝔏 𝔨).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) (g + (102 * Rc + (x + icost + 147))) := by
    rw [e]
    exact CostCls.In.join_add hgs hf
  have hle := base_splitRHSR 𝔅 sources gamma hg hh p 𝔨 n (C10PartsSchedule.widthAt sources 𝔨 n) _ hB
  have e2 : 102 * Rc + (icost + x + g + 147) = g + (102 * Rc + (x + icost + 147)) := by omega
  rw [e2]
  exact hle

end generic

/-! ## At the site (`B = siteBP4`, `Rc` = the ClassV4 reserve, index `k = kSelR (baseR siteBP4).ofBaseR capIndex`) -/

section site
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (capIndex : ParNat)

set_option hygiene false in
local notation "𝔅4" => SourceSkeleton.ClassV4.siteBP4 selector mask packets rows
set_option hygiene false in
local notation "ℜ4" => SourceSkeleton.ClassV4.siteR4 selector mask packets rows
set_option hygiene false in
local notation "𝔏4" => SourceSkeleton.ClassV4.siteL4 selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔜4" => SourceSkeleton.ClassV4.siteY4 selector mask packets rows
set_option hygiene false in
local notation "𝔜𝔉4" => SourceSkeleton.ClassV4.siteYF04 selector mask packets rows
set_option hygiene false in
local notation "𝔍4" => SourceSkeleton.ClassV4.siteI4 selector mask packets rows

/-- **`B`'s base RHS at index `k`** (the site's `refillCost = familyCost = firstCost`). -/
def Bsplit (k n : ℕ) : ℕ :=
  Admission.splitRHS ((baseR 𝔅4).dS sources gamma hg hh p) ((baseR 𝔅4).hT sources gamma hg hh p)
    ((baseR 𝔅4).hS sources gamma hg hh p) ((baseR 𝔅4).m sources gamma hg hh p) ((baseR 𝔅4).L sources gamma hg hh p)
    ((baseR 𝔅4).cP sources gamma hg hh p k) ((baseR 𝔅4).cT sources gamma hg hh p k) ((baseR 𝔅4).cS sources gamma hg hh p k) n
    (C10PartsSchedule.widthAt sources k n)

/-- The site index. -/
abbrev kS : ℕ := kSelR (baseR 𝔅4).ofBaseR capIndex sources gamma hg hh p

/-- **The refill rows' onset at the site** (fold into `xtra`). -/
def refOnS : ℕ := refOn printerOf (cVcN selector) (hVN selector) 𝔜4 𝔜𝔉4 𝔍4 sources gamma hg hh p capIndex
/-- **The first rows' onset at the site** (fold into `xtra`). -/
def firstOnS : ℕ := firstOn printerOf (cVcN selector) (hVN selector) 𝔜4 𝔜𝔉4 𝔍4 sources gamma hg hh p capIndex

theorem seamRows {vE vP : PCJd4d1d9d7d1fa4313_Production.Request → ℕ} (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) (g7cost : ℕ → ℕ) (rq : ℕ → PCJd4d1d9d7d1fa4313_Production.Request)
    (layA : ∀ m, Packets.Layout (decompositionOf sources) ((rq m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (rq m)))
    (factsA : ∀ m, ∀ row ∈ ((rq m).family (decompositionOf sources)).rows, Packets.PacketFacts (decompositionOf sources)
      ((rq m).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (rq m)) row)
    (capsAt : ℕ → RowCaps) (b vQ Mb Ms U0 WS RW BF N k n Rc Rk refillCost : ℕ)
    (hk : k = kS selector mask packets rows sources gamma hg hh p capIndex)
    (hn : refOnS selector mask packets rows sources gamma hg hh p capIndex ≤ n)
    (hRc : Rc = (ℜ4).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏4 ((ℜ4).hR sources gamma hg hh p)
      (C10PartsSchedule.widthAt sources k n))
    (hRk : Rk = 16 * (Rc + 1)) (hrefill : refillCost = Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hY : ∀ j, j < N → ((𝔜4).at sources gamma hg hh p 𝔏4 k).In 4 𝔏4 n (C10PartsSchedule.widthAt sources k n)
      (Rest.restCost se sp (fun _ => 0) (rq (j+1)) 0 b vQ
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          Mb Ms j +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (rq (j+1)) (layA (j+1))
          (factsA (j+1)) (capsAt (j+1))
          (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
            then Mb else Ms) U0 WS RW BF b 0))
    (hG : ∀ j, j < N → g7cost (j+1) ≤ RuntimeShape.tableClass 𝔏4 0 (C10PartsSchedule.widthAt sources k n)) :
    (∀ j, j < N → Rest.cursorCost j + 1 + g7cost (j+1) + 1 +
      (Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (rq (j+1)) (layA (j+1))
        (factsA (j+1)) (capsAt (j+1))
        (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          then Mb else Ms) U0 WS RW BF b (0)) + 1 ≤ Rc) ∧
    (∀ j, j < N → (Rest.restCost se sp g7cost (rq (j+1)) Rc b vQ
        (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
        Mb Ms j) + 1 +
      (Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (rq (j+1)) (layA (j+1))
        (factsA (j+1)) (capsAt (j+1))
        (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          then Mb else Ms) U0 WS RW BF b (0)) + 1 ≤ Rk) ∧
    (∀ j, j < N → (Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (rq (j+1))
        (layA (j+1)) (factsA (j+1)) (capsAt (j+1))
        (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          then Mb else Ms) U0 WS RW BF b
        ((4*Rk+7) + 1 + ((4*Rc+7) + 1 + ((Rest.restCost se sp g7cost (rq (j+1)) Rc b vQ
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          Mb Ms j) + 1 + Rest.refreshCost Rc)))) ≤ refillCost) := by
  subst hk hRk hrefill
  have key : ∀ j, j < N →
      Rest.restCost se sp g7cost (rq (j+1)) 0 b vQ
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          Mb Ms j +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (rq (j+1)) (layA (j+1))
          (factsA (j+1)) (capsAt (j+1))
          (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
            then Mb else Ms) U0 WS RW BF b 0 + 2 ≤ Rc ∧
      96 * Rc + (Rest.restCost se sp g7cost (rq (j+1)) 0 b vQ
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          Mb Ms j +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (rq (j+1)) (layA (j+1))
          (factsA (j+1)) (capsAt (j+1))
          (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
            then Mb else Ms) U0 WS RW BF b 0 + 115) ≤
        Bsplit selector mask packets rows sources gamma hg hh p (kS selector mask packets rows sources gamma hg hh p capIndex) n := by
    intro j hj
    have hw := refill_window printerOf (cVcN selector) (hVN selector) 𝔜4 𝔜𝔉4 𝔍4 sources gamma hg hh p capIndex n hn _ _ (hY j hj) (hG j hj)
    have hB := refill_in_B printerOf (cVcN selector) (hVN selector) 𝔜4 𝔜𝔉4 𝔍4 sources gamma hg hh p capIndex n Rc _ _ (le_of_eq hRc)
      (hY j hj) (hG j hj)
    replace hw := hw.trans (le_of_eq hRc.symm)
    have hs : Rest.restCost se sp g7cost (rq (j+1)) 0 b vQ
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          Mb Ms j =
        Rest.restCost se sp (fun _ => 0) (rq (j+1)) 0 b vQ
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((rq (j+1)).family (decompositionOf sources))).gs).length
          Mb Ms j + g7cost (j+1) := by
      simp only [Rest.restCost]
      omega
    rw [hs]
    exact ⟨by omega, le_trans (le_of_eq (by omega)) hB⟩
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · exact (Rest.windows_of_free se sp g7cost (rq (j+1)) Rc b vQ _ Mb Ms j _ (key j hj).1).1
  · exact (Rest.windows_of_free se sp g7cost (rq (j+1)) Rc b vQ _ Mb Ms j _ (key j hj).1).2
  · rw [refill3_fuel_eq]
    exact (key j hj).2

theorem firstRows {vE vP : PCJd4d1d9d7d1fa4313_Production.Request → ℕ} (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) (g7cost : ℕ → ℕ) (r0 : PCJd4d1d9d7d1fa4313_Production.Request)
    (lay0 : Packets.Layout (decompositionOf sources) (r0.family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) r0))
    (facts0 : ∀ row ∈ (r0.family (decompositionOf sources)).rows, Packets.PacketFacts (decompositionOf sources)
      (r0.family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) r0) row)
    (caps0 : RowCaps) (C icost w q Mb Ms U0 S Rw B v k n Rc Rk firstCost : ℕ)
    (hk : k = kS selector mask packets rows sources gamma hg hh p capIndex)
    (hn : firstOnS selector mask packets rows sources gamma hg hh p capIndex ≤ n)
    (hRc : Rc = (ℜ4).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏4 ((ℜ4).hR sources gamma hg hh p)
      (C10PartsSchedule.widthAt sources k n))
    (hRk : Rk = 16 * (Rc + 1)) (hfirst : firstCost = Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hY0 : ((𝔜𝔉4).at sources gamma hg hh p 𝔏4 k).In 4 𝔏4 n (C10PartsSchedule.widthAt sources k n)
      (6 * C + 0 + Rest.backCost se sp r0 0 w q
          (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length Mb Ms +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) r0 lay0 facts0 caps0
          (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length
            then Mb else Ms) U0 S Rw B v 0))
    (hI : ((𝔍4).at sources gamma hg hh p 𝔏4 k).In 4 𝔏4 n (C10PartsSchedule.widthAt sources k n) icost)
    (hG0 : g7cost 0 ≤ RuntimeShape.tableClass 𝔏4 0 (C10PartsSchedule.widthAt sources k n)) :
    (g7cost 0 + 1 + (Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) r0 lay0 facts0
        caps0 (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length
          then Mb else Ms) U0 S Rw B v (0)) + 1 ≤ Rc) ∧
    ((g7cost 0 + 1 + Rest.backCost se sp r0 Rc w q
        (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length Mb Ms) + 1 +
      (Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) r0 lay0 facts0
        caps0 (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length
          then Mb else Ms) U0 S Rw B v (0)) + 1 ≤ Rk) ∧
    ((Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) r0 lay0 facts0 caps0
        (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length
          then Mb else Ms) U0 S Rw B v
        (icost + 1 + ((4*Rk+7) + 1 + (((4*Rc+7) + 1 + ((4*Rc+7) + 1 + ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)))) + 1 +
          ((g7cost 0 + 1 + Rest.backCost se sp r0 Rc w q
            (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length Mb Ms) + 1 +
            (Rest.refreshCost Rc + 1 + ((2*Rc+4) + 1 + 1))))))) ≤ firstCost) := by
  subst hk hRk hfirst
  have hw := first_window printerOf (cVcN selector) (hVN selector) 𝔜4 𝔜𝔉4 𝔍4 sources gamma hg hh p capIndex n hn _ _ hY0 hG0
  have hB := first_in_B printerOf (cVcN selector) (hVN selector) 𝔜4 𝔜𝔉4 𝔍4 sources gamma hg hh p capIndex n Rc _ _ _ (le_of_eq hRc)
    hI hY0 hG0
  replace hw := hw.trans (le_of_eq hRc.symm)
  have hfree : g7cost 0 + 1 + Rest.backCost se sp r0 0 w q
      (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length Mb Ms +
      Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) r0 lay0 facts0 caps0
        (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) (r0.family (decompositionOf sources))).gs).length
          then Mb else Ms) U0 S Rw B v 0 + 2 ≤ Rc := by omega
  obtain ⟨h1, h2⟩ := Rest.first_windows_of_free se sp (g7cost 0) r0 Rc w q _ Mb Ms _ hfree
  refine ⟨h1, h2, ?_⟩
  rw [first3_fuel_eq]
  exact le_trans (le_of_eq (by omega)) hB

end site

end
end NearCubicWires.SourceFactorSel.ClauseCost
end

