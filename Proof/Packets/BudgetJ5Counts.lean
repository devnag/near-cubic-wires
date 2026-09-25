import Proof.Packets.BudgetJ5Compose

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
open NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size

section q
variable (sources : EightSources) (k : ℕ) {gamma : Real} (p : Parameters sources gamma)

/-- `q + 1 ≤ widthConst·(n+1)` raised to any power (SP's `widthAt_poly`). -/
theorem width_pow_le (n e : ℕ) :
    (C10PartsSchedule.widthAt sources k n + 1)^e ≤ C10PartsSchedule.widthConst sources k^e * (n+1)^e := by
  have h := SourcePhase.widthAt_poly sources k n
  rw [pow_one] at h
  calc (C10PartsSchedule.widthAt sources k n + 1)^e
      ≤ (C10PartsSchedule.widthConst sources k * (n+1))^e := Nat.pow_le_pow_left h e
    _ = C10PartsSchedule.widthConst sources k^e * (n+1)^e := mul_pow _ _ _

theorem one_le_widthConst : 1 ≤ C10PartsSchedule.widthConst sources k := by
  unfold C10PartsSchedule.widthConst
  omega

theorem nc_le_clauseAt {n : ℕ} (x : BitInput n) (bits : List Bool) :
    NC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ≤
      CloseoutFinalC10ModeNativeSchedule.clauseAt sources p (C10PartsSchedule.widthAt sources k n) :=
  CloseoutFinalC10ClauseBitsUniform.two_pow_clauseBits_le sources k p n x bits

theorem clauseAt_le_callAt (q : ℕ) :
    CloseoutFinalC10ModeNativeSchedule.clauseAt sources p q ≤
      CloseoutFinalC10ModeNativeSchedule.callAt sources p q := by
  unfold CloseoutFinalC10ModeNativeSchedule.callAt CloseoutFinalC10CallCountCap.siteCap
  have : 1 ≤ 16 * (CloseoutFinalC10ModeNativeSchedule.termAt sources p q + 1)^4 := by
    have := Nat.one_le_pow 4 (CloseoutFinalC10ModeNativeSchedule.termAt sources p q + 1) (by omega)
    omega
  exact Nat.le_mul_of_pos_right _ this

theorem callAt_le_jointCap (q : ℕ) :
    CloseoutFinalC10ModeNativeSchedule.callAt sources p q ≤
      CloseoutFinalC10ModeNativeSchedule.jointCap sources p q := by
  unfold CloseoutFinalC10ModeNativeSchedule.jointCap
  omega

/-- Past the schedule's onset, the joint cap is below `(q+1)^r` (`Selection.cap_le`). -/
theorem jointCap_le_pow (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ}
    (hn : S.onset ≤ n) :
    CloseoutFinalC10ModeNativeSchedule.jointCap sources p (C10PartsSchedule.widthAt sources k n) ≤
      (C10PartsSchedule.widthAt sources k n + 1)^S.exponent :=
  S.cap_le n hn

/-- **`hNq`/`hNn`**: the clause count below `(q+1)^r`, hence below `widthConst^r·(q+1)^r` and
`widthConst^r·(n+1)^r`. -/
theorem nc_le_pow (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ} (hn : S.onset ≤ n)
    (x : BitInput n) (bits : List Bool) :
    NC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ≤
      (C10PartsSchedule.widthAt sources k n + 1)^S.exponent :=
  ((nc_le_clauseAt sources k p x bits).trans (clauseAt_le_callAt sources p _)).trans
    ((callAt_le_jointCap sources p _).trans (jointCap_le_pow sources k p S hn))

theorem nc_le_q (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ} (hn : S.onset ≤ n)
    (x : BitInput n) (bits : List Bool) :
    NC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ≤
      C10PartsSchedule.widthConst sources k^S.exponent*(C10PartsSchedule.widthAt sources k n + 1)^S.exponent := by
  have h := nc_le_pow sources k p S hn x bits
  have h1 : 1 ≤ C10PartsSchedule.widthConst sources k^S.exponent :=
    Nat.one_le_pow _ _ (one_le_widthConst sources k)
  exact h.trans (Nat.le_mul_of_pos_left _ h1)

theorem nc_le_n (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ} (hn : S.onset ≤ n)
    (x : BitInput n) (bits : List Bool) :
    NC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ≤
      C10PartsSchedule.widthConst sources k^S.exponent*(n+1)^S.exponent :=
  (nc_le_pow sources k p S hn x bits).trans (width_pow_le sources k n S.exponent)

theorem capped_monomials_le (den : ℕ) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) :
    ((PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) j).monomials.length ≤
      CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n) := by
  have hc := nc_le_clauseAt sources k p x bits
  have hT : 2 * NC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) *
        xorTermBound (CompetitorRationalGap.zeta (constantsOf sources))
          (CloseoutFinalC10ModeNativeSchedule.sampleAt sources p (C10PartsSchedule.widthAt sources k n)) p.copies ≤
      CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n) := by
    unfold CloseoutFinalC10ModeNativeSchedule.termAt
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hc)
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [PCJd04de0277f804fcc_.coordinate_sym sources k _ p den x _ bits hs j]
    refine (CloseoutFinalC10ClauseBitsUniform.mapPolynomial_monomials_length _ _).trans_le ?_
    exact (CloseoutFinalC10ClauseBitsUniform.familyCoordinate_monomials_length_le rfl
      (P1Independent.CappedDecode.symFamilyOf sources k _ p den x _ bits) j).trans hT
  · rw [PCJd04de0277f804fcc_.coordinate_thr sources k _ p den x _ bits hs j]
    refine (CloseoutFinalC10ClauseBitsUniform.mapPolynomial_monomials_length _ _).trans_le ?_
    exact (CloseoutFinalC10ClauseBitsUniform.familyCoordinate_monomials_length_le rfl
      (P1Independent.CappedDecode.thrFamilyOf sources k _ p den x _ bits) j).trans hT

theorem calls_le_siteCap (den : ℕ) {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (ci : Fin (2^(pcppAt sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).clauseBits)) :
    (CloseoutFinalC10SupplierCalls.siteCalls ph (pcppAt sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
      (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits)
      C10TotalDecode.Atom.systematic ci).monomials.length ≤
      CloseoutFinalC10CallCountCap.siteCap
        (CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n)) := by
  have h := Admission.calls_poly ph (pcppAt sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
    (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits)
    C10TotalDecode.Atom.systematic ci
    (CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n))
    (CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n)) 0 0
    (by simp) (capped_monomials_le sources k p den x bits)
  unfold CloseoutFinalC10CallCountCap.siteCap
  simpa using h

/-- **S's per-clause `E`** (`Admission.siteFuel_inClasses`'s `hEn`/`hEq`): the calls of one clause are below
`(q+1)^r` past the schedule's onset. -/
theorem calls_le_pow (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (den : ℕ) {n : ℕ}
    (hn : S.onset ≤ n) (x : BitInput n) (bits : List Bool) (ph : Phase)
    (ci : Fin (2^(pcppAt sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).clauseBits)) :
    (CloseoutFinalC10SupplierCalls.siteCalls ph (pcppAt sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
      (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits)
      C10TotalDecode.Atom.systematic ci).monomials.length ≤
      (C10PartsSchedule.widthAt sources k n + 1)^S.exponent := by
  have h1 := calls_le_siteCap sources k p den x bits ph ci
  have hc : 1 ≤ CloseoutFinalC10ModeNativeSchedule.clauseAt sources p (C10PartsSchedule.widthAt sources k n) :=
    (Nat.one_le_two_pow).trans (nc_le_clauseAt sources k p x bits)
  have h2 : CloseoutFinalC10CallCountCap.siteCap
      (CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n)) ≤
      CloseoutFinalC10ModeNativeSchedule.callAt sources p (C10PartsSchedule.widthAt sources k n) := by
    unfold CloseoutFinalC10ModeNativeSchedule.callAt
    exact Nat.le_mul_of_pos_left _ hc
  exact (h1.trans h2).trans ((callAt_le_jointCap sources p _).trans (jointCap_le_pow sources k p S hn))

end q

section req
open NearCubicWires.RepairOrdinary.PCPPSubstitution NearCubicWires.RepairOrdinary.PCPPRequestBoundary

theorem sourceRequest_size_le (a : PointwisePCPPAlgorithm) {n r Q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin Q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF Q) :
    (sourceRequest a oracle projections formula).circuit.size +
      (sourceRequest a oracle projections formula).arity ≤ 2 * requestParameter a r Q oracle.size := by
  have hsub := compactSubstituted_size oracle projections formula
  have hsize : (sourceRequest a oracle projections formula).circuit.size ≤ requestParameter a r Q oracle.size := by
    change (PCPPRequestBoundary.request a (compactSubstituted oracle projections formula)).circuit.size ≤ _
    rw [request_size]
    unfold requestParameter
    omega
  have harity : (sourceRequest a oracle projections formula).arity ≤ requestParameter a r Q oracle.size := by
    change domain a r ≤ _
    unfold requestParameter
    omega
  omega

theorem sourceRequest_size_short (a : PointwisePCPPAlgorithm) {n r Q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin Q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF Q)
    (queryCoefficient queryDegree oracleDegree : ℕ) (hq : Q ≤ queryCoefficient*(r+1)^queryDegree)
    (ho : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound oracleDegree r) :
    (sourceRequest a oracle projections formula).circuit.size +
      (sourceRequest a oracle projections formula).arity ≤
      2 * CloseoutSourceCounts.shortRequest a queryCoefficient queryDegree oracleDegree r := by
  have hp : requestParameter a r Q oracle.size ≤
      CloseoutSourceCounts.shortRequest a queryCoefficient queryDegree oracleDegree r := by
    unfold CloseoutSourceCounts.shortRequest requestParameter
    gcongr
  have h := sourceRequest_size_le a oracle projections formula
  omega

end req

section reqAt
variable (sources : EightSources) (k : ℕ) {gamma : Real} (p : Parameters sources gamma)

/-- The length-only request bound at the native width. -/
abbrev shortAt (q : ℕ) : ℕ :=
  CloseoutSourceCounts.shortRequest (CloseoutLanguage.selectedPCPP sources)
    (SelectedRecoveryIntegration.fixedProjection sources).coefficient
    (SelectedRecoveryIntegration.fixedProjection sources).degrees.queries p.degree q

/-- **The actual request's size**, at every input and witness, below `2·shortAt q` (no onset). -/
theorem req_size_le {n : ℕ} (x : BitInput n) (bits : List Bool) :
    (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size +
      (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity ≤
      2 * shortAt sources p (C10PartsSchedule.widthAt sources k n) :=
  sourceRequest_size_short (CloseoutLanguage.selectedPCPP sources)
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)
    ((SelectedRecoveryIntegration.outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.queryAddressBits x)
    ((SelectedRecoveryIntegration.outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.decision x
      (fun _ => false))
    (SelectedRecoveryIntegration.fixedProjection sources).coefficient
    (SelectedRecoveryIntegration.fixedProjection sources).degrees.queries p.degree
    (CloseoutLanguage.selected_query_bound sources k (PolynomialClock.ordinaryClock k) n)
    (C10OracleSizeBound.oracleOf_size_le_cap sources k (PolynomialClock.ordinaryClock k) p.degree n bits
      (CloseoutFinalC10ClauseBitsUniform.nativeWidthOf_pos sources k n))

def reqC : ℕ := Classical.choose (CloseoutSourceCounts.shortRequest_polynomial (CloseoutLanguage.selectedPCPP sources)
    (SelectedRecoveryIntegration.fixedProjection sources).coefficient
    (SelectedRecoveryIntegration.fixedProjection sources).degrees.queries p.degree)
def reqE : ℕ := Classical.choose (Classical.choose_spec (CloseoutSourceCounts.shortRequest_polynomial
    (CloseoutLanguage.selectedPCPP sources)
    (SelectedRecoveryIntegration.fixedProjection sources).coefficient
    (SelectedRecoveryIntegration.fixedProjection sources).degrees.queries p.degree))

theorem shortAt_le (q : ℕ) : shortAt sources p q ≤ reqC sources p * (q+1)^reqE sources p :=
  (Classical.choose_spec (Classical.choose_spec (CloseoutSourceCounts.shortRequest_polynomial
    (CloseoutLanguage.selectedPCPP sources)
    (SelectedRecoveryIntegration.fixedProjection sources).coefficient
    (SelectedRecoveryIntegration.fixedProjection sources).degrees.queries p.degree))).2 q

theorem req_size_poly {n : ℕ} (x : BitInput n) (bits : List Bool) :
    (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size +
      (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity + 1 ≤
      (2*reqC sources p + 1) * C10PartsSchedule.widthConst sources k^reqE sources p * (n+1)^reqE sources p := by
  have h1 := req_size_le sources k p x bits
  have h2 := shortAt_le sources p (C10PartsSchedule.widthAt sources k n)
  have h3 := width_pow_le sources k n (reqE sources p)
  have h4 : 1 ≤ (C10PartsSchedule.widthAt sources k n + 1)^reqE sources p := Nat.one_le_pow _ _ (by omega)
  have h5 : (2*reqC sources p + 1) * (C10PartsSchedule.widthAt sources k n + 1)^reqE sources p ≤
      (2*reqC sources p + 1) * (C10PartsSchedule.widthConst sources k^reqE sources p * (n+1)^reqE sources p) :=
    Nat.mul_le_mul_left _ h3
  have e : (2*reqC sources p + 1) * (C10PartsSchedule.widthAt sources k n + 1)^reqE sources p =
      2*(reqC sources p * (C10PartsSchedule.widthAt sources k n + 1)^reqE sources p) +
        (C10PartsSchedule.widthAt sources k n + 1)^reqE sources p := by ring
  rw [Nat.mul_assoc]
  omega

end reqAt

end
end NearCubicWires.SourceBudget
end

