import Proof.SourceAssembly.SourceSkelKeptW

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

theorem K0Site_one (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) (hc1 : ∀ i, (ℭ mode i).val ≠ 1) (x : Fin V) (hx : x.val = 1) :
    K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC x = frameW := by
  rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC x (fun i => by rw [hx]; exact hc1 i)]
  simp [hx]

/-- **`hKt`**: the terminal's kept word is `1^NC`. -/
theorem K0Site_terminal (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) :
    K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC (terminalSite selector xtra mask packets rows sources gamma hg hh p V hV) = List.replicate NC true := by
  obtain ⟨hF, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  have hv : (terminalSite selector xtra mask packets rows sources gamma hg hh p V hV).val = 𝔬 + 53 := rfl
  rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC _ (fun i => by
    have := cache_nums selector xtra mask packets rows sources gamma hg hh p mode i; rw [hv]; omega)]
  rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega),
    if_pos rfl]

/-- **`hKres`** (the `hKhigh` form): a kept tape at or above `F` is a strip resident, with kept word `resW (x − sb)`. -/
theorem K0Site_strip (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) (x : Fin V) (hxF : (𝔡).F ≤ x.val) :
    K0Site selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC x =
      resW (x.val - ((𝔡).B + 29 + restPc (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW)) := by
  obtain ⟨hF, ho, hB, hU, hres', hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  have hc : ∀ i, (ℭ mode i).val ≠ x.val := fun i => by
    have := cache_nums selector xtra mask packets rows sources gamma hg hh p mode i; omega
  have ht : x ≠ terminalSite selector xtra mask packets rows sources gamma hg hh p V hV := fun h => by
    have hv := congrArg Fin.val h; change x.val = 𝔬 + 53 at hv; omega
  rw [K0Site_off selector xtra mask packets rows sources gamma hg hh p V hV mode frameW qW cdW resW Vv NC x hc]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg ht]

end kept

end
end NearCubicWires.SourceSkeleton.KeptW
end

