import Proof.CaseAnalysis.FinalStageContracts
import Proof.CaseAnalysis.FinalSiteCoefficientsFit
import Proof.CaseAnalysis.FinalFamilyMass

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 Relabelling the atoms of a canonical polynomial

`CircuitPolynomial Circuit degree` (`Proof/Circuits/ComponentwisePolynomial.lean`)
carries `Circuit : Type`, not a `CircuitFamily`, so a change of atom type along
any `F : Source → Target` is a pure list relabelling.  What has to be proved is
that it is semantics preserving; that is `mapPolynomial_value`. -/

/-- One monomial, relabelled.  Coefficients and occurrence multiplicities are
untouched: the paper's "occurrence-sensitive list of monomials" is preserved on
the nose, so no supplier call is merged or dropped. -/
def mapMonomial {Source Target : Type} {degree : ℕ} (F : Source → Target)
    (monomial : CircuitMonomial Source degree) : CircuitMonomial Target degree where
  coefficient := monomial.coefficient
  factors := monomial.factors.map F
  degree_le := by rw [List.length_map]; exact monomial.degree_le

/-- One polynomial, relabelled. -/
def mapPolynomial {Source Target : Type} {degree : ℕ} (F : Source → Target)
    (polynomial : CircuitPolynomial Source degree) : CircuitPolynomial Target degree where
  monomials := polynomial.monomials.map (mapMonomial F)

/-- A relabelled AND-four call is the original call at the pulled-back
evaluation.  `conjunctionBit` (`Proof/Foundations/SupplierPipeline.lean`) is
`List.all`, so the relabelling commutes with it. -/
theorem conjunctionBit_map {Source Target : Type} {q : ℕ} (F : Source → Target)
    (evaluate : Target → BitInput q → Bool) (factors : List Source)
    (input : BitInput q) :
    SupplierPipeline.conjunctionBit evaluate (factors.map F) input =
      SupplierPipeline.conjunctionBit (fun atom => evaluate (F atom)) factors input := by
  unfold SupplierPipeline.conjunctionBit
  induction factors with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp only [List.map_cons, List.all_cons, inductionHypothesis]

/-- **The relabelling is semantics preserving, monomial by monomial.** -/
theorem mapMonomial_value {Source Target : Type} {degree q : ℕ} (F : Source → Target)
    (evaluate : Target → BitInput q → Bool)
    (monomial : CircuitMonomial Source degree) (input : BitInput q) :
    (mapMonomial F monomial).value evaluate input =
      monomial.value (fun atom => evaluate (F atom)) input := by
  show (monomial.coefficient : ℝ) *
      bitAsReal (SupplierPipeline.conjunctionBit evaluate (monomial.factors.map F) input) =
    (monomial.coefficient : ℝ) *
      bitAsReal (SupplierPipeline.conjunctionBit (fun atom => evaluate (F atom))
        monomial.factors input)
  rw [conjunctionBit_map]

/-- **The relabelling is semantics preserving.**  This is the lemma that makes
`mapPolynomial` a transport rather than a carrier map: the relabelled polynomial
at `evaluate` is the original polynomial at `evaluate ∘ F`. -/
theorem mapPolynomial_value {Source Target : Type} {degree q : ℕ} (F : Source → Target)
    (evaluate : Target → BitInput q → Bool)
    (polynomial : CircuitPolynomial Source degree) (input : BitInput q) :
    (mapPolynomial F polynomial).value evaluate input =
      polynomial.value (fun atom => evaluate (F atom)) input := by
  show ((polynomial.monomials.map (mapMonomial F)).map fun monomial =>
      monomial.value evaluate input).sum =
    (polynomial.monomials.map fun monomial =>
      monomial.value (fun atom => evaluate (F atom)) input).sum
  rw [List.map_map]
  exact congrArg List.sum
    (List.map_congr_left fun monomial _ => mapMonomial_value F evaluate monomial input)

/-- The relabelling does not move coefficient mass. -/
theorem mapPolynomial_coefficientMass {Source Target : Type} {degree : ℕ}
    (F : Source → Target) (polynomial : CircuitPolynomial Source degree) :
    (mapPolynomial F polynomial).coefficientMass = polynomial.coefficientMass := by
  show ((polynomial.monomials.map (mapMonomial F)).map fun monomial =>
      |monomial.coefficient|).sum =
    (polynomial.monomials.map fun monomial => |monomial.coefficient|).sum
  rw [List.map_map]
  rfl

/-- The relabelling does not widen any coefficient. -/
theorem polynomialFits_mapPolynomial {Source Target : Type} {degree bits : ℕ}
    (F : Source → Target) {polynomial : CircuitPolynomial Source degree}
    (h : C10SiteCoefficientsFit.PolynomialFits bits polynomial) :
    C10SiteCoefficientsFit.PolynomialFits bits (mapPolynomial F polynomial) := by
  intro monomial hmonomial
  rcases List.mem_map.mp hmonomial with ⟨original, horiginal, rfl⟩
  exact h original horiginal

/-! ## §2 The transport -/

theorem coordinateExpands_map {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {Atom : Type}
    {circuit : BooleanCircuit limits.expectedArity}
    (pcpp : PointwisePCPP circuit)
    (eval : {q : ℕ} → Circuit q → BitInput q → Bool)
    (evaluate : Atom → BitInput limits.expectedArity → Bool)
    (F : Circuit limits.expectedArity → Atom)
    (hF : ∀ (atom : Circuit limits.expectedArity)
      (input : BitInput limits.expectedArity), evaluate (F atom) input = eval atom input)
    (family : CloseoutWitness.SumFamily Circuit wires description limits
      (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    CoordinateExpands pcpp evaluate
      (CloseoutWitness.SumFamily.value eval family)
      (fun j => mapPolynomial F (familyCoordinate rfl family j)) := by
  intro input j
  show (mapPolynomial F (familyCoordinate rfl family j)).value evaluate input =
      CloseoutWitness.SumFamily.value eval family input j
  rw [mapPolynomial_value]
  have hpull : (fun atom : Circuit limits.expectedArity => evaluate (F atom)) =
      (fun atom : Circuit limits.expectedArity => eval atom) := by
    funext atom
    funext point
    exact hF atom point
  rw [hpull]
  exact coordinateExpands_sumFamily_matched pcpp eval family input j

/-- The transported coordinate still obeys the decoder's coefficient-bit cap
(`CheckedLegalCircuitSum.coefficient_bits_le`). -/
theorem polynomialFits_map_familyCoordinate {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount target : ℕ} {Atom : Type}
    (F : Circuit target → Atom)
    (harity : limits.expectedArity = target)
    (family : CloseoutWitness.SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) :
    C10SiteCoefficientsFit.PolynomialFits limits.coefficientBitCap
      (mapPolynomial F (familyCoordinate harity family i)) :=
  polynomialFits_mapPolynomial F
    (C10SiteCoefficientsFit.polynomialFits_familyCoordinate harity family i)

/-- The transported coordinate still obeys the decoder's coefficient-mass cap
(`CheckedLegalCircuitSum.mass_le`). -/
theorem map_familyCoordinate_coefficientMass_le_cap {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount target : ℕ} {Atom : Type}
    (F : Circuit target → Atom)
    (harity : limits.expectedArity = target)
    (family : CloseoutWitness.SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) :
    (mapPolynomial F (familyCoordinate harity family i)).coefficientMass ≤
      limits.coefficientMassCap := by
  rw [mapPolynomial_coefficientMass]
  exact C10FamilyMass.familyCoordinate_coefficientMass_le_cap harity family i

/-! ## §3 The two decode embeddings, and their semantics -/

/-- `Atom.symmetric` is semantics preserving for `C10TotalDecode.evaluate`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`). -/
theorem evaluate_symmetric {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (atom : SupplierPipeline.NormalizedSymmetricThresholdCircuit n)
    (input : BitInput n) :
    C10TotalDecode.evaluate
        (C10TotalDecode.Atom.symmetric atom : C10TotalDecode.Atom pcpp) input =
      atom.eval input := rfl

/-- `Atom.threshold` is semantics preserving for `C10TotalDecode.evaluate`. -/
theorem evaluate_threshold {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (atom : SupplierPipeline.NormalizedThresholdThresholdCircuit n)
    (input : BitInput n) :
    C10TotalDecode.evaluate
        (C10TotalDecode.Atom.threshold atom : C10TotalDecode.Atom pcpp) input =
      atom.eval input := rfl

/-! ## §4 The decoded coordinate, at the decode union -/

noncomputable section

variable (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n ^ (k + 2)))
variable {gamma : ℝ} (p : Parameters sources gamma)
variable {n : ℕ} (x : BitInput n)
  (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n))
  (bits : List Bool)

def decodeCoordinate :
    Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle) →
      CircuitPolynomial (C10TotalDecode.Atom (pcppAt sources k clock x oracle)) 1 :=
  if CloseoutWitness.BoundedFields.symmetric bits then
    fun j => mapPolynomial C10TotalDecode.Atom.symmetric
      (familyCoordinate rfl (C10TotalDecode.symFamilyOf sources k clock p x oracle bits) j)
  else
    fun j => mapPolynomial C10TotalDecode.Atom.threshold
      (familyCoordinate rfl (C10TotalDecode.thrFamilyOf sources k clock p x oracle bits) j)

theorem decodeCoordinate_sym (hs : CloseoutWitness.BoundedFields.symmetric bits = true)
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    decodeCoordinate sources k clock p x oracle bits j =
      mapPolynomial C10TotalDecode.Atom.symmetric
        (familyCoordinate rfl
          (C10TotalDecode.symFamilyOf sources k clock p x oracle bits) j) := by
  unfold decodeCoordinate
  rw [if_pos hs]
  rfl

theorem decodeCoordinate_thr (hs : ¬ CloseoutWitness.BoundedFields.symmetric bits = true)
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    decodeCoordinate sources k clock p x oracle bits j =
      mapPolynomial C10TotalDecode.Atom.threshold
        (familyCoordinate rfl
          (C10TotalDecode.thrFamilyOf sources k clock p x oracle bits) j) := by
  unfold decodeCoordinate
  rw [if_neg hs]
  rfl

/-! ## §5 The two branch policies share the coefficient caps

`CloseoutSampledWitness.symmetricLimits` (`Proof/CaseAnalysis/SampledWitness.lean`)
and `thresholdLimits` (`Proof/CaseAnalysis/SampledWitness.lean`) differ only in `wireCap` and `descriptionCap`;
`expectedArity`, `termCap`, `coefficientBitCap` and `coefficientMassCap` are the
same `Average.limits` (`Proof/CaseAnalysis/WitnessAverage.lean`) arguments.  So a
single bound serves both branches, and `hcoefficients` / `hmass` need no case
split at the consumer. -/

/-! ## §6 The three `StageBlock` fields, in their verbatim shapes -/

variable (m : ℕ) (y : BitInput m) (record : List Bool)

/-- **`StageData.coordinate`.**  Exactly the field's type at
`Proof/CaseAnalysis/FinalStageContracts.lean`. -/
def stageCoordinate :
    Fin ((C10TailComposeUniform.pcppOf sources k p y record).systematicBits +
      (C10TailComposeUniform.pcppOf sources k p y record).auxiliaryBits) →
      CircuitPolynomial (C10TailComposeUniform.Atoms sources k p y record) 1 :=
  decodeCoordinate sources k (PolynomialClock.ordinaryClock k) p y
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree m record) record

/-- **`StageData.mass`.**  Exactly the field's type at
`Proof/CaseAnalysis/FinalStageContracts.lean`, at the decoder's own mass cap. -/
def stageMass (phase : CloseoutRowsOriginalSchedule.Phase) : ℝ :=
  C10FamilyMass.massBound
    (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p y
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree m record)) phase

end


end NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
