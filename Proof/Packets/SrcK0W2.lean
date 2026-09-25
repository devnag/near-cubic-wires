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
local notation "𝔘" => USite selector xtra mask packets rows sources gamma hg hh p
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
local notation "ℭ𝔖" => cacheSite selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)
set_option hygiene false in
local notation "𝔠𝔞𝔭" => capC sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) x
  (C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
    (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits)

def K0W' (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) : Phase → ℕ → Fin (𝔘 + 1) → List Bool := fun ph ci =>
  Function.update (K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci) (ℭ𝔖 mode 15)
    (List.replicate 𝔠𝔞𝔭 false)

/-- **`hK15`'s word**: the cache-15 word of `K0W'` is `0^capC`. -/
theorem K0W'_c15 (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) (ci : ℕ) :
    K0W' selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci (ℭ𝔖 mode 15) = List.replicate 𝔠𝔞𝔭 false :=
  Function.update_self _ _ _

/-- Off the query copy's cache tape, `K0W'` is `K0W`. -/
theorem K0W'_ne (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) (ci : ℕ) (y : Fin (𝔘 + 1))
    (hy : y ≠ ℭ𝔖 mode 15) :
    K0W' selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci y =
      K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci y :=
  Function.update_of_ne hy _ _

/-- On the entry kept set `KcW` (which excludes `c15`), `K0W'` is `K0W`. -/
theorem K0W'_Kc (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) (ci : ℕ) (y : Fin (𝔘 + 1))
    (hy : KcW selector xtra mask packets rows sources gamma hg hh p mode y) :
    K0W' selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci y =
      K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci y :=
  K0W'_ne selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci y hy.2.1

/-- **`K0W'` in K0Site form**: the kept words at the cache words `Function.update (cdAt ci) 15 (0^capC)`. -/
theorem K0W'_eq_K0Site (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) (ci : ℕ) (y : Fin (𝔘 + 1)) :
    K0W' selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci y =
      K0Site selector xtra mask packets rows sources gamma hg hh p (𝔘 + 1) (Nat.le_succ _) mode (RepairOrdinary.frame bits)
        (ZeroPadding.pad 𝔠𝔞𝔭 (SourceSteps.qwordAt sources p 𝔨 n x bits ci))
        (Function.update (SourceSteps.cdAt sources p 𝔨 n x bits ci) 15 (List.replicate 𝔠𝔞𝔭 false))
        (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n (C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n)) 𝔙
        (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) y := by
  by_cases h15 : y = ℭ𝔖 mode 15
  · subst h15
    rw [K0W'_c15, K0Site_cache, Function.update_self]
  · rw [K0W'_ne selector xtra mask packets rows sources gamma hg hh p mode n x bits ph ci y h15]
    show K0Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode (RepairOrdinary.frame bits)
        (ZeroPadding.pad 𝔠𝔞𝔭 (SourceSteps.qwordAt sources p 𝔨 n x bits ci)) (SourceSteps.cdAt sources p 𝔨 n x bits ci)
        (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n (C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n)) 𝔙
        (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) y = _
    by_cases hc : ∃ i, ℭ𝔖 mode i = y
    · obtain ⟨i, hi⟩ := hc
      subst hi
      have hi15 : i ≠ 15 := fun e => h15 (by rw [e])
      rw [K0Site_cache, K0Site_cache, Function.update_of_ne hi15]
    · have hc' : ∀ i, (ℭ mode i).val ≠ y.val := fun i h =>
        hc ⟨i, Fin.ext ((cacheSite_val selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode i).trans h)⟩
      rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p _ _ mode _ _ _ _ _ _ y hc',
        K0Site_off selector xtra mask packets rows sources gamma hg hh p _ _ mode _ _ _ _ _ _ y hc']

end site

end
end NearCubicWires.SourceStart.EntryW
end

