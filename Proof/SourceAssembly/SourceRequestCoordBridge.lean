import Proof.SourceAssembly.SourceFactorSelModes
import Proof.SourceAssembly.SourceRequestTermReader

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CoordBridge
open NearCubicWires CanonicalBinary CanonicalWitnessCodec SupplierPipeline ComponentwisePolynomial SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.SourceRequest.TermReader
noncomputable section

/-! ## The codec, inverted on the reader's words -/

theorem termOf_code {Circuit : CanonicalWitnessCodec.CircuitFamily} (codec : CanonicalCircuitCodec Circuit) {n : Nat}
    (t : LegalCircuitTerm Circuit n) : termOf (t.code codec) = some (t.coefficient, codec.encode t.circuit) := by
  simp [termOf, LegalCircuitTerm.code, decodeTaggedList_encode, decodeCanonicalRational_encode]

theorem mapM_termOf {Circuit : CanonicalWitnessCodec.CircuitFamily} (codec : CanonicalCircuitCodec Circuit) {n : Nat}
    (terms : List (LegalCircuitTerm Circuit n)) :
    (terms.map (·.code codec)).mapM termOf = some (terms.map fun t => (t.coefficient, codec.encode t.circuit)) := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons, List.mapM_cons, termOf_code, ih]
    rfl

theorem rawSum_code {Circuit : CanonicalWitnessCodec.CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    (d : LegalCircuitSumDescription Circuit) :
    rawSum (d.code codec) = some (d.terms.map fun t => (t.coefficient, codec.encode t.circuit)) := by
  unfold rawSum LegalCircuitSumDescription.code
  rw [decodeTaggedList_encode]
  show (decodeBalancedList (encodeBalancedList (d.terms.map (·.code codec)))).bind (fun ts => ts.mapM termOf) = _
  rw [decodeBalancedList_encode, Option.bind_some, mapM_termOf]

/-- **The reader's raw term list of variable `i` is the decoded family's sum `i`.** -/
theorem rawTerms_of_decode {Circuit : CanonicalWitnessCodec.CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    {wires description : {n : Nat} → Circuit n → Nat} {limits : LegalSumLimits} {count : Nat}
    (bits : List Bool) (family : SumFamily Circuit wires description limits count)
    (h : SumFamily.decode codec wires description limits count
      (RadixSemantics.value (BoundedFields.family bits)) = some family) (i : Fin count) :
    rawTerms bits i.val = some ((family.getSum i).value.terms.map fun t => (t.coefficient, codec.encode t.circuit)) := by
  have hc := SumFamily.code_of_decode codec h
  have hi : i.val < family.sums.length := by rw [family.length_eq]; exact i.isLt
  unfold rawTerms
  rw [← hc]
  simp only [SumFamily.code, decodeBalancedList_encode, Option.bind_some, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some]
  simp only [Option.bind_some, CheckedLegalCircuitSum.code, rawSum_code, SumFamily.getSum]
  rfl

/-! ## The interface the composition reads -/

/-- An atom's code as the reader prints it (the codec of its kind; `0` for a systematic atom). -/
def codeOfAtom {n : Nat} {circuit : BooleanCircuit n} {pcpp : PointwisePCPP circuit} :
    C10TotalDecode.Atom pcpp → Nat
  | .systematic _ => 0
  | .symmetric c => encodeNormalizedSymmetricThresholdCircuit c
  | .threshold c => encodeNormalizedThresholdThresholdCircuit c

/-- **The coordinate is what the reader reads**: per proof variable `j`, the raw term list `ts` exists, the monomials are
`ts` term by term (coefficient, one factor whose code is the term's code), and every factor is an original atom of `mode`. -/
def CoordReads (mode : Bool) {n : Nat} {circuit : BooleanCircuit n} {pcpp : PointwisePCPP circuit} {V : Nat}
    (coordinate : Fin V → CircuitPolynomial (C10TotalDecode.Atom pcpp) 1) (bits : List Bool) : Prop :=
  ∀ j : Fin V, ∃ ts : List (ℚ × Nat), rawTerms bits j.val = some ts ∧
    (coordinate j).monomials.map (fun mo => (mo.coefficient, mo.factors.map codeOfAtom)) =
      ts.map (fun t => (t.1, [t.2])) ∧
    ∀ mo ∈ (coordinate j).monomials, ∀ a ∈ mo.factors, SourceFactorSel.Modes.kindOf mode (some a) = .orig

theorem transport_sym {a b : Nat} {β : Type} (e : a = b)
    (terms : List (LegalCircuitTerm NormalizedSymmetricThresholdCircuit a)) (G : ℚ → Nat → β) :
    (transportTerms e terms).map (fun t => G t.coefficient (encodeNormalizedSymmetricThresholdCircuit t.circuit)) =
      terms.map (fun t => G t.coefficient (encodeNormalizedSymmetricThresholdCircuit t.circuit)) := by
  subst e; rfl

theorem transport_thr {a b : Nat} {β : Type} (e : a = b)
    (terms : List (LegalCircuitTerm NormalizedThresholdThresholdCircuit a)) (G : ℚ → Nat → β) :
    (transportTerms e terms).map (fun t => G t.coefficient (encodeNormalizedThresholdThresholdCircuit t.circuit)) =
      terms.map (fun t => G t.coefficient (encodeNormalizedThresholdThresholdCircuit t.circuit)) := by
  subst e; rfl

theorem sym_encode {n : Nat} (c : NormalizedSymmetricThresholdCircuit n) :
    symmetricCircuitCodec.encode c = encodeNormalizedSymmetricThresholdCircuit c := by
  simp only [symmetricCircuitCodec]
theorem thr_encode {n : Nat} (c : NormalizedThresholdThresholdCircuit n) :
    thresholdCircuitCodec.encode c = encodeNormalizedThresholdThresholdCircuit c := by
  simp only [thresholdCircuitCodec]

/-- One symmetric coordinate at the reader's words. -/
theorem reads_sym {n : Nat} {circuit : BooleanCircuit n} {pcpp : PointwisePCPP circuit}
    {wires description : {q : Nat} → NormalizedSymmetricThresholdCircuit q → Nat} {limits : LegalSumLimits} {count : Nat}
    (harity : limits.expectedArity = n) (bits : List Bool)
    (family : SumFamily NormalizedSymmetricThresholdCircuit wires description limits count)
    (h : SumFamily.decode symmetricCircuitCodec wires description limits count
      (RadixSemantics.value (BoundedFields.family bits)) = some family) (i : Fin count) :
    ∃ ts : List (ℚ × Nat), rawTerms bits i.val = some ts ∧
      (mapPolynomial (C10TotalDecode.Atom.symmetric (pcpp := pcpp)) (familyCoordinate harity family i)).monomials.map
        (fun mo => (mo.coefficient, mo.factors.map codeOfAtom)) = ts.map (fun t => (t.1, [t.2])) ∧
      ∀ mo ∈ (mapPolynomial (C10TotalDecode.Atom.symmetric (pcpp := pcpp)) (familyCoordinate harity family i)).monomials,
        ∀ a ∈ mo.factors, SourceFactorSel.Modes.kindOf true (some a) = .orig := by
  refine ⟨_, rawTerms_of_decode symmetricCircuitCodec bits family h i, ?_, ?_⟩
  · have h1 : (mapPolynomial (C10TotalDecode.Atom.symmetric (pcpp := pcpp)) (familyCoordinate harity family i)).monomials.map
        (fun mo => (mo.coefficient, mo.factors.map codeOfAtom)) =
        (transportTerms ((family.getSum i).arity_eq.trans harity) (family.getSum i).value.terms).map
          (fun t => (t.coefficient, [encodeNormalizedSymmetricThresholdCircuit t.circuit])) := by
      simp only [mapPolynomial, familyCoordinate, linearPolynomial, List.map_map]
      rfl
    rw [h1, transport_sym _ _ (fun c k => (c, [k])), List.map_map]
    simp only [Function.comp_def, sym_encode]
  · intro mo hmo a ha
    simp only [mapPolynomial, familyCoordinate, linearPolynomial, List.mem_map] at hmo
    obtain ⟨m0, ⟨t, _, rfl⟩, rfl⟩ := hmo
    simp [mapMonomial] at ha
    subst ha
    rfl

/-- One threshold coordinate at the reader's words. -/
theorem reads_thr {n : Nat} {circuit : BooleanCircuit n} {pcpp : PointwisePCPP circuit}
    {wires description : {q : Nat} → NormalizedThresholdThresholdCircuit q → Nat} {limits : LegalSumLimits} {count : Nat}
    (harity : limits.expectedArity = n) (bits : List Bool)
    (family : SumFamily NormalizedThresholdThresholdCircuit wires description limits count)
    (h : SumFamily.decode thresholdCircuitCodec wires description limits count
      (RadixSemantics.value (BoundedFields.family bits)) = some family) (i : Fin count) :
    ∃ ts : List (ℚ × Nat), rawTerms bits i.val = some ts ∧
      (mapPolynomial (C10TotalDecode.Atom.threshold (pcpp := pcpp)) (familyCoordinate harity family i)).monomials.map
        (fun mo => (mo.coefficient, mo.factors.map codeOfAtom)) = ts.map (fun t => (t.1, [t.2])) ∧
      ∀ mo ∈ (mapPolynomial (C10TotalDecode.Atom.threshold (pcpp := pcpp)) (familyCoordinate harity family i)).monomials,
        ∀ a ∈ mo.factors, SourceFactorSel.Modes.kindOf false (some a) = .orig := by
  refine ⟨_, rawTerms_of_decode thresholdCircuitCodec bits family h i, ?_, ?_⟩
  · have h1 : (mapPolynomial (C10TotalDecode.Atom.threshold (pcpp := pcpp)) (familyCoordinate harity family i)).monomials.map
        (fun mo => (mo.coefficient, mo.factors.map codeOfAtom)) =
        (transportTerms ((family.getSum i).arity_eq.trans harity) (family.getSum i).value.terms).map
          (fun t => (t.coefficient, [encodeNormalizedThresholdThresholdCircuit t.circuit])) := by
      simp only [mapPolynomial, familyCoordinate, linearPolynomial, List.map_map]
      rfl
    rw [h1, transport_thr _ _ (fun c k => (c, [k])), List.map_map]
    simp only [Function.comp_def, thr_encode]
  · intro mo hmo a ha
    simp only [mapPolynomial, familyCoordinate, linearPolynomial, List.mem_map] at hmo
    obtain ⟨m0, ⟨t, _, rfl⟩, rfl⟩ := hmo
    simp [mapMonomial] at ha
    subst ha
    rfl

section leaf
variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n ^ (k + 2)))
variable {gamma : Real} (p : Parameters sources gamma) (den : Nat)
variable {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) (bits : List Bool)

theorem coordReads_sym (hs : BoundedFields.symmetric bits = true)
    (family : P1Independent.CappedDecode.SymFamily sources k clock p den x oracle)
    (h : SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits (P1Independent.CappedDecode.symLimits sources k clock p den x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    CoordReads true (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) bits := by
  intro j
  rw [PCJd04de0277f804fcc_.coordinate_sym sources k clock p den x oracle bits hs j,
    P1Independent.CappedDecode.symFamilyOf_pin sources k clock p den x oracle bits family h]
  exact reads_sym rfl bits family h j

theorem coordReads_thr (hs : ¬ BoundedFields.symmetric bits = true)
    (family : P1Independent.CappedDecode.ThrFamily sources k clock p den x oracle)
    (h : SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    CoordReads false (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) bits := by
  intro j
  rw [PCJd04de0277f804fcc_.coordinate_thr sources k clock p den x oracle bits hs j,
    P1Independent.CappedDecode.thrFamilyOf_pin sources k clock p den x oracle bits family h]
  exact reads_thr rfl bits family h j

end leaf

end
end NearCubicWires.SourceRequest.CoordBridge

