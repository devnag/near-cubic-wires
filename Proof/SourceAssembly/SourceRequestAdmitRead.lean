import Proof.SourceAssembly.SourcePhaseEntry
import Proof.SourceAssembly.SourceRequestCoordBridge

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.AdmitRead
open NearCubicWires SourceInterfaces RepairSource RepairRepresentation
open SelectedRecoveryIntegration CanonicalWitnessCodec SupplierPipeline
open NearCubicWires.RepairOrdinary
open CloseoutWitness CloseoutWitness.SelectedSource
open private decode_cast size_cast from Proof.CaseAnalysis.WitnessDyadicGuards
noncomputable section

theorem decoded (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2)))
    (cutoff D G copies symDen thrDen : Nat) (delta : Rat)
    {n : Nat} (x : BitInput n) (bits : List Bool)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n))
    (hdecode : decodeBooleanCircuit _ (RadixSemantics.value (BoundedFields.oracle bits))=some oracle)
    (hn : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (hp : BoundedFamily.passed (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
      k (hierarchy sources k clock).coefficient (padding sources k clock) cutoff D G copies
      symDen thrDen delta (code sources k clock) x bits (Nat.le_max_right _ _)=true) :
    let a := CloseoutLanguage.selectedPCPP sources
    let rq := CloseoutWitnessPolicy.request sources k clock x oracle
    let q := (outer sources k clock).result.pcp.nativeWidth n
    let R := CloseoutLanguage.clauseWidth D q
    let V := CloseoutWitnessPolicy.variableCount sources k clock x oracle
    (∃ family, SumFamily.decode symmetricCircuitCodec
      NormalizedSymmetricThresholdCircuit.wireCount NormalizedSymmetricThresholdCircuit.descriptionBits
      (CloseoutSampledWitness.symmetricLimits a rq R copies ⌊wireScale (1/(symDen:Real)) 5 q⌋₊ delta)
      V (RadixSemantics.value (BoundedFields.family bits))=some family ∧
      BoundedFields.symmetric bits=true) ∨
    (∃ family, SumFamily.decode thresholdCircuitCodec
      NormalizedThresholdThresholdCircuit.wireCount NormalizedThresholdThresholdCircuit.descriptionBits
      (CloseoutSampledWitness.thresholdLimits a rq R copies ⌊wireScale (1/(thrDen:Real)) 9 q⌋₊ delta)
      V (RadixSemantics.value (BoundedFields.family bits))=some family ∧
      BoundedFields.symmetric bits=false) := by
  obtain ⟨_hlen, _header, _native, actual, ha, hf⟩ :=
    (BoundedFamily.passed_exact (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
      k (hierarchy sources k clock).coefficient (padding sources k clock) cutoff D G copies
      symDen thrDen delta (code sources k clock) x bits (Nat.le_max_right _ _)).mp hp
  have same := Option.some.inj (ha.symm.trans (decode_cast (width sources k clock x) hdecode))
  subst actual
  have arity := CloseoutWitnessPolicy.input_cutoff_arity sources k clock x oracle hn
  have clause := congrArg (CloseoutLanguage.clauseWidth D) arity
  have cap (den e : Nat) : LegalPolicy.W e den (CloseoutWitnessPolicy.request sources k clock x oracle).arity =
      ⌊wireScale (1/(den:Real)) e ((outer sources k clock).result.pcp.nativeWidth n)⌋₊ := by
    rw [arity]
    exact (CloseoutRawRows.naturalWireCap_floor den e _).symm
  unfold ColdFamily.decodedFamily at hf
  rw [request_eq sources k clock x oracle] at hf
  cases hm : BoundedFields.symmetric bits
  · rw [BoundedFamily.exponent, BoundedFamily.denominator, hm] at hf
    simp only [Bool.false_eq_true, if_false] at hf
    rw [cap, clause] at hf
    obtain ⟨family, hf⟩ := hf
    exact Or.inr ⟨family, hf, rfl⟩
  · rw [BoundedFamily.exponent, BoundedFamily.denominator, hm] at hf
    simp only [if_true] at hf
    rw [cap, clause] at hf
    obtain ⟨family, hf⟩ := hf
    exact Or.inl ⟨family, hf, rfl⟩

section site
open NearCubicWires.RepairSource.CloseoutFinal (Parameters)
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k : Nat)
  {n : Nat} (x : BitInput n) (bits : List Bool)

/-- **`hlen` from the admission**: the admitted witness is at most `n/16` bits long. -/
theorem hlen_site
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (P1TopDown.ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (P1TopDown.WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) :
    16 * bits.length ≤ n :=
  ((BoundedFamily.passed_exact (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
    (hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient (padding sources k (PolynomialClock.ordinaryClock k))
    (P1TopDown.WorkspaceSelectedAdmission.coldCutoff sources) p.clauseDegree p.degree p.copies den den
    (CompetitorRationalGap.zeta (CloseoutFinal.constantsOf sources)) (code sources k (PolynomialClock.ordinaryClock k)) x bits
    (Nat.le_max_right _ _)).mp hp).1

/-- **The admitted oracle is the totalized one**: the oracle field decodes, at the native width, to `oracleOf … p.degree n bits`. -/
theorem oracle_decode
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (P1TopDown.ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (P1TopDown.WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) :
    decodeBooleanCircuit ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)
        (RadixSemantics.value (BoundedFields.oracle bits)) =
      some (CloseoutFinal.C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) := by
  obtain ⟨A, L, -, -, hc, -⟩ :=
    P1TopDown.ControllerCappedSelected.selected_run sources p den hden k (PolynomialClock.ordinaryClock k) 0 n x bits
  obtain ⟨_H, oracle, hdecode, hsize, -⟩ := hc hp
  let hw := width sources k (PolynomialClock.ordinaryClock k) x
  let selectedOracle := cast (congrArg BooleanCircuit hw) oracle
  have decodedO : decodeBooleanCircuit _ (RadixSemantics.value (BoundedFields.oracle bits)) =
      some selectedOracle := decode_cast hw.symm hdecode
  have sized : selectedOracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound p.degree
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n) := by
    have h := size_cast hw.symm oracle
    change selectedOracle.size = oracle.size at h
    exact h.le.trans (hsize.trans (congrArg (RecoveryScheduleEnvelope.oracleSizeBound p.degree) hw).le)
  rw [CloseoutFinal.C10TotalDecode.oracleOf_pin sources k (PolynomialClock.ordinaryClock k) p.degree n bits
    selectedOracle decodedO sized]
  exact decodedO

/-- **`hread` from the admission, in the flag's mode**: the site coordinate reads as the witness's raw terms. -/
theorem coordReads_adm
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (P1TopDown.ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (P1TopDown.WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) :
    CoordBridge.CoordReads (BoundedFields.symmetric bits)
      (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (CloseoutFinal.C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) bits := by
  have hdec := oracle_decode sources p den hden k x bits hp
  have hd := decoded sources k (PolynomialClock.ordinaryClock k) (P1TopDown.WorkspaceSelectedAdmission.coldCutoff sources)
    p.clauseDegree p.degree p.copies den den (CompetitorRationalGap.zeta (CloseoutFinal.constantsOf sources)) x bits
    (CloseoutFinal.C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) hdec hN hp
  dsimp only at hd
  cases hm : BoundedFields.symmetric bits
  · rcases hd with ⟨family, h, hs⟩ | ⟨family, h, _⟩
    · rw [hm] at hs; exact absurd hs (by decide)
    · exact CoordBridge.coordReads_thr sources k (PolynomialClock.ordinaryClock k) p den x
        (CloseoutFinal.C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
        (by rw [hm]; decide) family h
  · rcases hd with ⟨family, h, _⟩ | ⟨family, h, hs⟩
    · exact CoordBridge.coordReads_sym sources k (PolynomialClock.ordinaryClock k) p den x
        (CloseoutFinal.C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits hm family h
    · rw [hm] at hs; exact absurd hs (by decide)

theorem coordReads_site (r scratch : Nat)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (P1TopDown.ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (P1TopDown.WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) :
    CoordBridge.CoordReads (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)
      (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (CloseoutFinal.C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) bits := by
  obtain ⟨hmode, -⟩ := SourcePhase.penalty_bank sources p den hden k r scratch n x bits hp
  rw [hmode]
  exact coordReads_adm sources p den hden k x bits hp hN

end site

end
end NearCubicWires.SourceRequest.AdmitRead

