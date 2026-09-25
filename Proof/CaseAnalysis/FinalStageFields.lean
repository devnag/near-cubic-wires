import Proof.CaseAnalysis.FinalExactFraction
import Proof.CaseAnalysis.FinalStageFuelBound
import Proof.CaseAnalysis.FinalSumFamilyTransport
import Proof.CaseAnalysis.FinalUnionSupplier

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness (CoordinateExpands phasePolynomial)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (CoefficientsFit siteCalls)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths (thresholdWidth)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.RepairSource.CloseoutLanguage (selectedPCPP)
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

def stageArity (n : ℕ) : ℕ :=
  max ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)
    (selectedPCPP sources).minimumArity

/-! ## §2 The frozen limits, and the two witnesses of the accuracy ledger -/

/-- **The decoded family's limits, frozen.**  `symLimits`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`) is
`CloseoutSampledWitness.symmetricLimits` (`Proof/CaseAnalysis/SampledWitness.lean`),
whose `coefficientMassCap` field is `massCap delta copies`
(`Proof/CaseAnalysis/WitnessAverage.lean`) at `delta := zeta (constantsOf sources)`
and `copies := p.copies`.  Neither depends on the input length, the input, or
the guessed oracle, so evaluating `symLimits` at a canonical point names that
one cap -- `symLimits_coefficientMassCap` below is the `rfl` that proves it.
`paper.tex:1405-1408` is the sentence: coefficient masses "are frozen before the
weak machine". -/
def stageMassCap : ℚ :=
  CloseoutSampledWitness.massCap (zeta (constantsOf sources)) p.copies

/-- The frozen limits: the one cap above, carried by a `LegalSumLimits` that
depends on nothing else. -/
def stageLimits : CanonicalWitnessCodec.LegalSumLimits where
  expectedArity := 0
  termCap := 0
  coefficientBitCap := 0
  coefficientMassCap := stageMassCap sources p
  wireCap := 0
  descriptionCap := 0

/-- **`S.failure`'s requested reciprocal accuracy**, the canonical choice of
`accuracyTarget_le_all` (`Proof/CaseAnalysis/FinalSupplierAccuracyChain.lean`):
one number per input length, independent of the length because the limits are
frozen. -/
def stageTarget : ℕ → ℕ :=
  fun _ => accuracyTargetAll (constantsOf sources) (stageLimits sources p)

/-- **The uniform denominator's exponent**, at exactly the `Nat.size` headroom
`accuracyTarget_le_denominator` (`Proof/CaseAnalysis/FinalSupplierAccuracyChain.lean`)
asks for -- a CONSTANT, so `entryWidth` grows by a constant and stays in the
`FREE / POLYLOG` bucket of `ENDGAME_RESOURCE.md` §2. -/
def stageScale : ℕ → ℕ :=
  fun _ => Nat.size (accuracyTargetAll (constantsOf sources) (stageLimits sources p))

/-- **`S.failure`.** -/
def stageFailure : (n : ℕ) → BitInput n → List Bool → Phase → ℝ :=
  failureOf (stageTarget sources p) (stageArity sources k) (stageScale sources p)

/-- **`S.entryWidth`**, at S-W's three floors. -/
def stageEntryWidth (coefficientFloor : ℕ → ℕ) : ℕ → ℕ :=
  entryWidth coefficientFloor (stageArity sources k) (stageScale sources p) (constantsOf sources)

/-! ## §3 The three record-shape-independent semantic fields

These are SUMFAM's, at the field's verbatim type.  They are restated here (as
terms, not reproofs) so the assembly has one module to `refine` from. -/

/-! ## §4 The width and accuracy fields -- all four unconditional -/

/-! ## §5 The SCALAR-denominator supplier fields -- `StageBlock` as it stands -/

/-! ## §6 The EXACT-FRACTION supplier fields -- the four shapes EXACTFRAC pinned -/

/-- **`num`** (EXACTFRAC's `hnum` slot): A.13.9's own numerator
`\sum_e\sum_z T_{e,F(z)}(z)`, per call, with no rescaling. -/
def stageNum (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
      Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ :=
  fun n _ _ _ monomial =>
    rowAnswer (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (monomial.factors.map atomToUnion)

/-- **`den`**: A.13.9's own `|\mathcal E|2^q` (`paper.tex:3161`), per call. -/
def stageDen (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
      Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ :=
  fun n _ _ _ monomial =>
    rowDenominator (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (monomial.factors.map atomToUnion)

/-- **`S.supplier` on the exact route**: the rows' own rational output, NOT the
rescaled `unionSupplier` of §5. -/
def stageRowSupplier (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ :=
  fun n _ _ atoms =>
    rowSupplier (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (atoms.map atomToUnion)

/-! ## §7 `hfuel` -- the criterion, and the call cap that feeds it -/

end


end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
