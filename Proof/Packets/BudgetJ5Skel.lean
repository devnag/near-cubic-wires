import Proof.Packets.BudgetJ5Split
import Proof.SourceAssembly.SourceSkelTop

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceBudget
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size

theorem sumWidth_poly (m b n bC bE eC eE : ℕ) (hb : b + 1 ≤ bC*(n+1)^bE) (hE : m + 1 ≤ eC*(n+1)^eE) :
    CompetitorSumWidth.width m (CompetitorRationalDecision.width b) + 1 ≤ (3*(eC*bC)+1)*(n+1)^(eE+bE) := by
  unfold CompetitorSumWidth.width CompetitorRationalDecision.width
  have h1 : (m+1)*(2*b+2+1) ≤ (m+1)*(3*(b+1)) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (m+1)*(3*(b+1)) ≤ (eC*(n+1)^eE)*(3*(bC*(n+1)^bE)) := Nat.mul_le_mul hE (by omega)
  have e : (eC*(n+1)^eE)*(3*(bC*(n+1)^bE)) = 3*(eC*bC)*(n+1)^(eE+bE) := by rw [pow_add]; ring
  have h3 : 1 ≤ (n+1)^(eE+bE) := Nat.one_le_pow _ _ (by omega)
  have e2 : (3*(eC*bC)+1)*(n+1)^(eE+bE) = 3*(eC*bC)*(n+1)^(eE+bE) + (n+1)^(eE+bE) := by ring
  omega

section atK
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)

theorem poly_len_le (den : ℕ) {k : ℕ} (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ}
    (hn : S.onset ≤ n) (x : BitInput n) (bits : List Bool) (ph : Phase) :
    (Poly sources p k den (PolynomialClock.ordinaryClock k) n x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length ≤
      C10PartsSchedule.widthConst sources k^(S.exponent+S.exponent)*(n+1)^(S.exponent+S.exponent) := by
  have h := (poly_length_le _ (fun c => calls_le_pow sources k p S den hn x bits ph c)).trans
    (Nat.mul_le_mul_right _ (nc_le_pow sources k p S hn x bits))
  rw [← pow_add] at h
  exact h.trans (width_pow_le sources k n _)

theorem fits_at (den : ℕ) {k : ℕ} (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ}
    (hn : S.onset ≤ n) (x : BitInput n) (bits : List Bool) (sf : Phase → ℕ) (dS hT hS m L cP cT cS : ℕ)
    (hsf : ∀ ph, Admission.InClasses dS hT hS m L n (C10PartsSchedule.widthAt sources k n) cP cT cS (sf ph)) :
    PCJ374c44bb8b7f47d9_.branchFuel (costOf sources p den k S.exponent n x bits sf)
        (fun ph => CompetitorSumWidth.width
          (Poly sources p k den (PolynomialClock.ordinaryClock k) n x
            (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length
          (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k S.exponent n))) + 2 ≤
      (sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).fuel (CloseoutLanguage.selectedPCPP sources) n
        (C10PartsSchedule.widthAt sources k n) := by
  have hb : C10PartsSchedule.entryWidthSchedule sources k S.exponent n + 1 ≤
      (C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^S.exponent)*
        (n+1)^S.exponent := by
    have h := SourcePhase.b_poly sources k S.exponent n (C10PartsSchedule.widthConst sources k) 1
      (by simpa using SourcePhase.widthAt_poly sources k n)
    simpa using h
  have hee : (n+1)^S.exponent ≤ (n+1)^(S.exponent+S.exponent) := Nat.pow_le_pow_right (by omega) (by omega)
  have hx : ∀ ph, C10PartsSchedule.entryWidthSchedule sources k S.exponent n +
      (Poly sources p k den (PolynomialClock.ordinaryClock k) n x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length + 1 ≤
      (C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^S.exponent +
        C10PartsSchedule.widthConst sources k^(S.exponent+S.exponent))*(n+1)^(S.exponent+S.exponent) := by
    intro ph
    have hE := poly_len_le sources p den S hn x bits ph
    have hm := Nat.mul_le_mul_left
      (C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^S.exponent) hee
    have ex : (C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^S.exponent +
          C10PartsSchedule.widthConst sources k^(S.exponent+S.exponent))*(n+1)^(S.exponent+S.exponent) =
        (C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^S.exponent)*
          (n+1)^(S.exponent+S.exponent) +
        C10PartsSchedule.widthConst sources k^(S.exponent+S.exponent)*(n+1)^(S.exponent+S.exponent) := by ring
    omega
  have hw : ∀ ph, CompetitorSumWidth.width
      (Poly sources p k den (PolynomialClock.ordinaryClock k) n x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length
      (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k S.exponent n)) + 1 ≤
      (3*((C10PartsSchedule.widthConst sources k^(S.exponent+S.exponent) + 1)*
        (C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^S.exponent)) + 1)*
        (n+1)^((S.exponent+S.exponent)+S.exponent) := by
    intro ph
    have hE : (Poly sources p k den (PolynomialClock.ordinaryClock k) n x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length + 1 ≤
        (C10PartsSchedule.widthConst sources k^(S.exponent+S.exponent) + 1)*(n+1)^(S.exponent+S.exponent) := by
      have h0 := poly_len_le sources p den S hn x bits ph
      have h2 : 1 ≤ (n+1)^(S.exponent+S.exponent) := Nat.one_le_pow _ _ (by omega)
      have ex : (C10PartsSchedule.widthConst sources k^(S.exponent+S.exponent) + 1)*(n+1)^(S.exponent+S.exponent) =
          C10PartsSchedule.widthConst sources k^(S.exponent+S.exponent)*(n+1)^(S.exponent+S.exponent) +
            (n+1)^(S.exponent+S.exponent) := by ring
      omega
    exact sumWidth_poly _ _ n _ S.exponent _ (S.exponent+S.exponent) hb hE
  have hpen : 4*C10PartsSchedule.entryWidthSchedule sources k S.exponent n + 23 ≤
      (sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).eC*
        (n+1)^(sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).eE := by
    have h := penalty_entry_le sources k S.exponent n
    have hp : (n+1)^S.exponent ≤ (n+1)^(sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).eE :=
      Nat.pow_le_pow_right (by omega) (by simp only [sourceConsts]; omega)
    have hc := Nat.mul_le_mul (show (4*C10PartsSchedule.thresholdFloor sources + 23 +
        4*C10PartsSchedule.widthConst sources k^S.exponent) ≤
        (sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).eC by simp only [sourceConsts]; omega) hp
    exact h.trans hc
  have hlat : 2*capC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) + 4 ≤
      (sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).eC*
        (n+1)^(sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).eE := by
    have h := later_entry_le sources k p x bits
    have hp : (n+1)^(reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources)) ≤
        (n+1)^(sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).eE :=
      Nat.pow_le_pow_right (by omega) (by simp only [sourceConsts]; omega)
    have hc := Nat.mul_le_mul (show (2*PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP sources)*
        sizeC sources k p^PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources) + 4) ≤
        (sourceConsts sources k p S.exponent dS hT hS m L cP cT cS).eC by simp only [sourceConsts]; omega) hp
    exact h.trans hc
  refine fits_generic (sourceConsts sources k p S.exponent dS hT hS m L cP cT cS)
    (CloseoutLanguage.selectedPCPP sources) _ _
    (NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
    ((req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size +
      (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)
    (C10PartsSchedule.entryWidthSchedule sources k S.exponent n)
    (entryFuelOf sources p k S.exponent n x bits) sf
    (fun ph => (Poly sources p k den (PolynomialClock.ordinaryClock k) n x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length)
    (cpOf sources p k n x bits sf)
    (nc_le_n sources k p S hn x bits) (nc_le_q sources k p S hn x bits)
    (req_size_poly sources k p x bits) hx ?_ hsf (fun ph => le_refl _) (fun ph => rfl) hw
  intro ph
  cases ph
  · exact hpen
  · exact hlat
  · exact hlat

end atK

/-- S's site class, per parameter tuple: EXPONENTS (and the divisor and live scale) fixed before the hierarchy
index, COEFFICIENTS at the index `k` (the type enforces the order of choices). -/
structure SiteClassFam where
  dS : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  hT : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  hS : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  m : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  L : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  cP : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ
  cT : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ
  cS : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ

/-- The schedule exponent (chosen before `k`). -/
abbrev rSel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) : ℕ :=
  (CloseoutFinalC10ModeNativeSchedule.selected sources p 0).exponent

section holes

end holes

end
end NearCubicWires.SourceBudget
end

