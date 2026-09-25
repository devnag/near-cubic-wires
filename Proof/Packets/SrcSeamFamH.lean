import Proof.Packets.SrcSeamNums

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceStart.SeamRP
open NearCubicWires.SourceBudget
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton
noncomputable section

theorem family_hcost_all (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den k : ℕ) (hden : 1 ≤ den) (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ}
    (hn : S.onset ≤ n) (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (x : BitInput n) (bits : List Bool)
    (mode : Bool) (ph : Phase) (L : ℕ)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
    (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
      (tgt sources p) mode selector)
    (deg : ℕ → ℕ) (hdeg : ∀ j, deg j ≤ C10PartsSchedule.widthAt sources k n)
    (printer : WilliamsAlgorithm) (V cVc hV : ℕ)
    (hVc : V ≤ cVc * RuntimeShape.tableClass L hV (C10PartsSchedule.widthAt sources k n))
    (Dw dC : ℕ) (hDw : Dw + 1 ≤ dC * (C10PartsSchedule.entryWidthSchedule sources k S.exponent n + 1))
    (m : ℕ) (c : CostCls) (hc : (famClsAt printer sources p k S.exponent cVc hV dC).Le c) :
    ∀ j,
      PCJ1fef9807c6954e94_Native.f_budget printer (P1TopDownPaidReusableReserves.workspace printer V)
          (TraceData.rowWidthOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
            (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
            (tgt sources p) mode deg j)
          (C10PartsSchedule.entryWidthSchedule sources k S.exponent n)
          ((TraceData.dsOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
            (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
            (tgt sources p) mode selector compiler lay j).map PCJ9eff70d512234a4c_Fixed.datumValue).length + 1 +
        (2*Dw+4+1+(2*PCJ1fef9807c6954e94_Native.e_emitCost (C10PartsSchedule.entryWidthSchedule sources k S.exponent n)+2)+1+
          CloseoutFinalC10AppendPositioning.budget (C10PartsSchedule.entryWidthSchedule sources k S.exponent n)
            (prefixEntries (phaseE sources p den k x bits mode ph L) ci.val ++
              (TraceData.entriesOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
                (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
                (tgt sources p) mode).take j).length) ≤
        Admission.splitRHS c.dP c.hT c.hS m L c.cP c.cT c.cS n (C10PartsSchedule.widthAt sources k n) := by
  intro j
  -- the arity is the width
  have hq : (req sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity =
      C10PartsSchedule.widthAt sources k n :=
    Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) hN
  -- call `j` is admitted
  have hadm : Admission.Admitted den p.clauseDegree
      (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j) := by
    have h0 := Admission.trace_atoms_admitted sources k (PolynomialClock.ordinaryClock k) p den x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits hN ph ci _
      (List.Perm.refl _) j
    have h1 : Admission.Admitted den p.clauseDegree
        (((TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).map
          (fun m => m.factors)).getD j []) := h0
    have hf : ((TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).map (fun m => m.factors)).getD j [] =
        SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j := by
      by_cases hlt : j < (TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length
      · exact TraceData.factors_getD _ ph ci j hlt
      · have h1' : ((TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).map (fun m => m.factors)).getD j [] = [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          rfl
        have hlen : (SourceRequest.FactorLoop.monomials (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length = (TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length := rfl
        have h2' : SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j = [] := by
          unfold SourceRequest.FactorLoop.factorsAt
          rw [List.getElem?_eq_none (by omega)]
        rw [h1', h2']
    exact (congrArg (Admission.Admitted den p.clauseDegree) hf).mp h1
  set W := C10PartsSchedule.widthConst sources k with hWdef
  set qn := C10PartsSchedule.widthAt sources k n with hqn
  have hW1 : 1 ≤ W := one_le_widthConst sources k
  -- the row count
  have hq' : (CloseoutWitnessPolicy.request sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity = qn := hq
  have hrows0 := call_rows_le (target := tgt sources p) sources L mode hden _ hadm
  have hrows : (Packets.request sources L (tgt sources p) mode
        (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j)).rows.length + 1 ≤
      rowsC (decompositionOf sources) p.clauseDegree (tgt sources p) * (qn+1)^rowsE (decompositionOf sources) p.clauseDegree (tgt sources p) := by
    refine hrows0.trans (le_of_eq ?_)
    rw [hq']
  have hlen : ((TraceData.dsOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
      (tgt sources p) mode selector compiler lay j).map PCJ9eff70d512234a4c_Fixed.datumValue).length =
      (Packets.request sources L (tgt sources p) mode
        (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j)).rows.length := by
    simp [TraceData.dsOf, dataList]
  set N := ((TraceData.dsOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
      (tgt sources p) mode selector compiler lay j).map PCJ9eff70d512234a4c_Fixed.datumValue).length with hNdef
  set rC := rowsC (decompositionOf sources) p.clauseDegree (tgt sources p)
  set rE := rowsE (decompositionOf sources) p.clauseDegree (tgt sources p)
  have hNq : N ≤ (rC * W^rE)*(qn+1)^rE := by
    have h1 : N ≤ rC*(qn+1)^rE := by omega
    have h2 : rC ≤ rC * W^rE := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hW1)
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hNn : N ≤ (rC * W^rE)*(n+1)^rE := by
    have h1 : N ≤ rC*(qn+1)^rE := by omega
    have h2 := width_pow_le sources k n rE
    calc N ≤ rC*(qn+1)^rE := h1
      _ ≤ rC*(W^rE*(n+1)^rE) := Nat.mul_le_mul_left _ h2
      _ = (rC*W^rE)*(n+1)^rE := by ring
  -- the widths
  have hrw := call_rowWidth_le (target := tgt sources p) sources L mode hden _ hadm (deg j)
    (le_of_le_of_eq (hdeg j) hq'.symm)
  set b := C10PartsSchedule.entryWidthSchedule sources k S.exponent n with hbdef
  set bC := betaC (decompositionOf sources) p.clauseDegree
  set bE := betaE (decompositionOf sources) p.clauseDegree
  have hrwn : TraceData.rowWidthOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
      (tgt sources p) mode deg j ≤ ((2*bC+10)*W^(bE+2))*(n+1)^(bE+2+S.exponent) := by
    have h0 : TraceData.rowWidthOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
        (tgt sources p) mode deg j ≤ (2*bC+10)*(qn+1)^(bE+2) := by
      unfold TraceData.rowWidthOf TraceData.lenOf
      refine hrw.trans (le_of_eq ?_)
      rw [hq']
    have h1 := width_pow_le sources k n (bE+2)
    have h2 : (n+1)^(bE+2) ≤ (n+1)^(bE+2+S.exponent) := Nat.pow_le_pow_right (by omega) (by omega)
    calc _ ≤ (2*bC+10)*(qn+1)^(bE+2) := h0
      _ ≤ (2*bC+10)*(W^(bE+2)*(n+1)^(bE+2)) := Nat.mul_le_mul_left _ h1
      _ ≤ (2*bC+10)*(W^(bE+2)*(n+1)^(bE+2+S.exponent)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = ((2*bC+10)*W^(bE+2))*(n+1)^(bE+2+S.exponent) := by ring
  have hb : b + 1 ≤ (C10PartsSchedule.thresholdFloor sources + 1 + W^S.exponent)*(n+1)^(bE+2+S.exponent) := by
    have h0 := SourcePhase.b_poly sources k S.exponent n W 1 (by simpa using SourcePhase.widthAt_poly sources k n)
    have h2 : (n+1)^(1*S.exponent) ≤ (n+1)^(bE+2+S.exponent) := Nat.pow_le_pow_right (by omega) (by omega)
    exact h0.trans (Nat.mul_le_mul_left _ h2)
  have hcnt := entry_count_le sources p den k S hn x bits mode ph L ci j
  rw [← hbdef] at hcnt
  have hx : TraceData.rowWidthOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
      (tgt sources p) mode deg j + b + Dw +
      (prefixEntries (phaseE sources p den k x bits mode ph L) ci.val ++
        (TraceData.entriesOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
          (tgt sources p) mode).take j).length + 1 ≤
      famXC sources p k S.exponent dC * (n+1)^famXE sources p S.exponent := by
    have hcnt' : (prefixEntries (phaseE sources p den k x bits mode ph L) ci.val ++
        (TraceData.entriesOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L
          (tgt sources p) mode).take j).length ≤ b := hcnt
    have hDb : Dw + 1 + (b + 1) + (b + 1) ≤ (dC + 2)*(b+1) := by
      have : (dC + 2)*(b+1) = dC*(b+1) + 2*(b+1) := by ring
      omega
    have hDb2 : (dC + 2)*(b+1) ≤
        (dC + 2)*((C10PartsSchedule.thresholdFloor sources + 1 + W^S.exponent)*(n+1)^(bE+2+S.exponent)) :=
      Nat.mul_le_mul_left _ hb
    have e : famXC sources p k S.exponent dC * (n+1)^famXE sources p S.exponent =
        ((2*bC+10)*W^(bE+2))*(n+1)^(bE+2+S.exponent) +
          (dC + 2)*((C10PartsSchedule.thresholdFloor sources + 1 + W^S.exponent)*(n+1)^(bE+2+S.exponent)) := by
      simp only [famXC, famXE]
      ring
    rw [e]
    omega
  exact (family_entry_in printer V cVc hV hVc _ b N Dw _ (rC * W^rE) rE (famXC sources p k S.exponent dC)
    (famXE sources p S.exponent) hNn hNq hx).mono_cls hc

end
end NearCubicWires.SourceStart.SeamRP

namespace NearCubicWires.SourceStart.SeamRP
open NearCubicWires.SourceBudget
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton
noncomputable section

/-! ## The site's family class, its clock condition and the onset -/

section site
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

abbrev famW (k : ℕ) : CostCls :=
  famClsAt (printerOf sources) sources p k (SourceSteps.rBsel sources p)
    (SourceBudget.Params.cVcN selector sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) 22

theorem famSite_dP_le_kW :
    (famW selector sources gamma hg hh p (ParamsV4.kW selector mask packets rows sources gamma hg hh p)).dP + 1 ≤
      ParamsV4.kW selector mask packets rows sources gamma hg hh p + 2 := by
  have h := ParamsV4.BW_dP_le_kW selector mask packets rows sources gamma hg hh p
  have h2 : (famW selector sources gamma hg hh p (ParamsV4.kW selector mask packets rows sources gamma hg hh p)).dP ≤
      (ParamsV4.BW selector mask packets rows).dP sources gamma hg hh p :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  omega

/-- **The site family class's table exponent is below the reserve's** (`siteR4.hR` = the maximum of its classes' `+ 2`). -/
theorem famSite_hT_le (k : ℕ) :
    (famW selector sources gamma hg hh p k).hT + 2 ≤ (ClassV4.siteR4 selector mask packets rows).hR sources gamma hg hh p :=
  Nat.add_le_add_right (le_trans (le_max_left _ _) (le_max_left _ _)) 2

def hfamOn (k L : ℕ) (hk : (famW selector sources gamma hg hh p k).dP + 1 ≤ k + 2) : ℕ :=
  max (Classical.choose (hfamH_at sources k (famW selector sources gamma hg hh p k) 2 L le_rfl hk)) (SourceSteps.selR sources p k).onset

/-- **`hfamH`'s onset at the site** (index `kW`, live scale `siteL4`): the onset to FOLD into `xtra`. -/
def hfamOnW : ℕ :=
  hfamOn selector sources gamma hg hh p (ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p) (famSite_dP_le_kW selector mask packets rows sources gamma hg hh p)

/-- Past `hfamOnW`, `hfamH_RP`'s `hn` holds at the site index `kSite xtra` (any onset `xtra`; `kSite xtra = kW`), with the site clock proof. -/
theorem hfamOn_site (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (n : ℕ)
    (h : hfamOnW selector mask packets rows sources gamma hg hh p ≤ n) :
    hfamOn selector sources gamma hg hh p (FirstW.kSite selector xtra mask packets rows sources gamma hg hh p)
      (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p) (famSite_dP_le_kW selector mask packets rows sources gamma hg hh p) ≤ n := h

end site

end
end NearCubicWires.SourceStart.SeamRP

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
open NearCubicWires.SourceSteps
namespace NearCubicWires.SourceStart.SeamRP
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section nums
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

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
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw (oldAt coordC ph ci sources L tgtC modeC b Dw) Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "vdX" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "𝔏𝔖" => ClassV4.siteL4 selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "ℜ𝔖" => (ClassV4.siteR4 selector mask packets rows).C sources gamma hg hh p *
  RuntimeShape.tableClass (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)
    ((ClassV4.siteR4 selector mask packets rows).hR sources gamma hg hh p) (C10PartsSchedule.widthAt sources k n)

theorem hfamH_RP (hg : 0 < gamma) (hh : gamma < 1/2) (ph : Phase)
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s) (g7cost : Nat → Nat)
    (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat) (Rc Rk b : Nat)
    (lay : TraceData.LayoutFamily coordC ph ci sources L tgtC modeC selector)
    (capsAt : Nat → RowCaps)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordC ph ci L tgtC modeC m) (layA m) (factsA m) (capsAt m))    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (old : Nat → List Bool)
    (familyCost firstCost counterReserve : Nat)
    (cW cQ cB cS refillCost N : Nat)
    (hk : (famW selector sources gamma hg hh p k).dP + 1 ≤ k + 2)
    (hn : hfamOn selector sources gamma hg hh p k 𝔏𝔖 hk ≤ n)
    (hr : r = SourceSteps.rBsel sources p)
    (hLe : L = 𝔏𝔖) (hRce : Rc = ℜ𝔖) (hbe : b = C10PartsSchedule.entryWidthSchedule sources k r n)
    (hVe : V = SourceBudget.Params.VvOf selector sources p 𝔏𝔖 (C10PartsSchedule.widthAt sources k n))
    (hDwe : Dw = NearCubicWires.SourceConstruction.InitRun.D0 b)
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg vQ L) :
    ∀ j, j < N → ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))) (layA (j+1)) (factsA (j+1))) vWS vRW vBF (dataList (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))) (layA (j+1)) (factsA (j+1))).length i + (fuelOf 𝒞 b vdX (j+1)) + 1 ≤ Rc := by
  subst hLe hRce hbe hVe hDwe
  unfold hfamOn at hn
  simp only [max_le_iff] at hn
  obtain ⟨n1, n2⟩ := hn
  have hcut := SourceSteps.selR_cutoff sources p k n2
  have hq : (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity =
      C10PartsSchedule.widthAt sources k n :=
    Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x _ hcut
  have hdeg : ∀ j, degOf sources selector coordC ph ci 𝔏𝔖 tgtC modeC lay j ≤ C10PartsSchedule.widthAt sources k n := fun j =>
    (SourceSteps.degOf_le_arity selector sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ph ci 𝔏𝔖 lay hlay j).trans
      (le_of_eq hq)
  have hb1 : 1 ≤ C10PartsSchedule.entryWidthSchedule sources k r n := by
    unfold C10PartsSchedule.entryWidthSchedule C10PartsSchedule.widthPower
    have := Nat.one_le_pow r (C10PartsSchedule.widthAt sources k n + 1) (Nat.succ_pos _)
    omega
  have hS : (SourceSteps.selR sources p k).exponent = r := hr.symm
  have hDw : NearCubicWires.SourceConstruction.InitRun.D0 (C10PartsSchedule.entryWidthSchedule sources k r n) + 1 ≤
      22 * (C10PartsSchedule.entryWidthSchedule sources k (SourceSteps.selR sources p k).exponent n + 1) := by
    rw [hS]
    unfold NearCubicWires.SourceConstruction.InitRun.D0 NearCubicWires.SourceConstruction.InitEnc.rr
    omega
  intro j _ i
  refine Classical.choose_spec (NearCubicWires.SourceBudget.hfamH_at sources k (famW selector sources gamma hg hh p k) 2 𝔏𝔖 le_rfl hk) n n1 _ ?_
    ((ClassV4.siteR4 selector mask packets rows).C sources gamma hg hh p) ((ClassV4.siteR4 selector mask packets rows).hR sources gamma hg hh p)
    le_rfl (famSite_hT_le selector mask packets rows sources gamma hg hh p k) _ _ _ _ _ _ i
  have hfam := family_hcost_all sources p den k hden (SourceSteps.selR sources p k) n2 hcut x bits modeC ph 𝔏𝔖 ci selector compiler lay
    (degOf sources selector coordC ph ci 𝔏𝔖 tgtC modeC lay) hdeg (printerOf sources)
    (SourceBudget.Params.VvOf selector sources p 𝔏𝔖 (C10PartsSchedule.widthAt sources k n))
    (SourceBudget.Params.cVcN selector sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) le_rfl
    _ 22 hDw 2 (famW selector sources gamma hg hh p k) ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩ (j+1)
  rw [hS] at hfam
  exact hfam

end nums

end
end NearCubicWires.SourceStart.SeamRP
end

