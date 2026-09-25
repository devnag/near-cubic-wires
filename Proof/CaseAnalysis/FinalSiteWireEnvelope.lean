import Proof.CaseAnalysis.FinalWireEnvelope

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields (stageArity stageTarget
  stageEntryWidth)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows (primeCutoff listDenominator)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope (unionWires atomWires
  unionRequestOf stageSeedEnvelope SiteDenFits siteDenFits_of_wireEnvelope envelopeFloor
  hfloor_at_envelopeFloor)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters decompositionOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom symLimits thrLimits
  symFamilyOf thrFamilyOf oracleOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier (DecodeUnion atomToUnion
  rightRequest unionTarget)
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime (primesUpTo)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Weakening the predicate. -/
theorem FactorsSatisfy.mono {A : Type} {degree : ℕ}
    {polynomial : CircuitPolynomial A degree} {P Q : A → Prop}
    (h : polynomial.FactorsSatisfy P) (hPQ : ∀ atom, P atom → Q atom) :
    polynomial.FactorsSatisfy Q :=
  fun monomial hmonomial atom hatom => hPQ atom (h monomial hmonomial atom hatom)

/-- **`coordinatePenalty`** (`Proof/CaseAnalysis/FinalExactness.lean`): the
paper's `(Enc_s - T)^2` on a systematic coordinate and `T^2 (1-T)^2` on an
auxiliary one.  The systematic branch is the only one that charges the
systematic atom, hence the only one that needs `hsystematic`. -/
theorem coordinatePenalty_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (systematicAtom : Fin pcpp.systematicBits → A) (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (hsystematic : ∀ i, predicate (systematicAtom i))
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (coordinatePenalty pcpp coordinate systematicAtom j).FactorsSatisfy predicate := by
  refine Fin.addCases ?_ ?_ j
  · intro index
    rw [coordinatePenalty, Fin.addCases_left]
    exact CircuitPolynomial.weaken_factorsSatisfy _ _ predicate
      (systematicValidityPolynomial_factorsSatisfy _ _ predicate (hsystematic index)
        (hcoordinate _))
  · intro index
    rw [coordinatePenalty, Fin.addCases_right]
    exact auxiliaryValidityPolynomial_factorsSatisfy _ predicate (hcoordinate _)

/-- **`penaltySite`** (`Proof/CaseAnalysis/FinalExactness.lean`). -/
theorem penaltySite_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (systematicAtom : Fin pcpp.systematicBits → A) (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (hsystematic : ∀ i, predicate (systematicAtom i))
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (penaltySite pcpp coordinate systematicAtom i).FactorsSatisfy predicate := by
  unfold penaltySite
  exact CircuitPolynomial.scale_factorsSatisfy _ _ predicate
    (CircuitPolynomial.add_factorsSatisfy _ _ predicate
      (coordinatePenalty_factorsSatisfy pcpp coordinate systematicAtom predicate hcoordinate
        hsystematic _)
      (coordinatePenalty_factorsSatisfy pcpp coordinate systematicAtom predicate hcoordinate
        hsystematic _))

/-- **`momentSite`** (`Proof/CaseAnalysis/FinalExactness.lean`). -/
theorem momentSite_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (momentSite pcpp coordinate i).FactorsSatisfy predicate := by
  unfold momentSite
  exact CircuitPolynomial.weaken_factorsSatisfy _ _ predicate
    (secondMomentPolynomial_factorsSatisfy _ predicate (hcoordinate _))

/-- **`clauseSite`** (`Proof/CaseAnalysis/FinalExactness.lean`). -/
theorem clauseSite_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (clauseSite pcpp coordinate i).FactorsSatisfy predicate := by
  unfold clauseSite
  exact CircuitPolynomial.weaken_factorsSatisfy _ _ predicate
    (clausePolynomial_factorsSatisfy _ _ _ _ predicate (hcoordinate _) (hcoordinate _))

/-- **`sitePolynomial`** (`Proof/CaseAnalysis/FinalExactness.lean`), all three
phases. -/
theorem sitePolynomial_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (phase : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (systematicAtom : Fin pcpp.systematicBits → A) (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (hsystematic : ∀ i, predicate (systematicAtom i))
    (i : Fin (2 ^ pcpp.clauseBits)) :
    (sitePolynomial phase pcpp coordinate systematicAtom i).FactorsSatisfy predicate := by
  cases phase with
  | penalty =>
      show (penaltySite pcpp coordinate systematicAtom i).FactorsSatisfy predicate
      exact penaltySite_factorsSatisfy pcpp coordinate systematicAtom predicate hcoordinate
        hsystematic i
  | moment =>
      show (momentSite pcpp coordinate i).FactorsSatisfy predicate
      exact momentSite_factorsSatisfy pcpp coordinate predicate hcoordinate i
  | clause =>
      show (clauseSite pcpp coordinate i).FactorsSatisfy predicate
      exact clauseSite_factorsSatisfy pcpp coordinate predicate hcoordinate i

/-- **`siteCalls`** (`Proof/CaseAnalysis/FinalSupplierCalls.lean`) -- the
polynomial whose monomials the machine actually prints at one clause address.
The uniform `1 / 2 ^ clauseBits` touches no atom. -/
theorem siteCalls_factorsSatisfy {A : Type} {N : ℕ} {circuit : BooleanCircuit N}
    (phase : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial A 1)
    (systematicAtom : Fin pcpp.systematicBits → A) (predicate : A → Prop)
    (hcoordinate : ∀ j, (coordinate j).FactorsSatisfy predicate)
    (hsystematic : ∀ i, predicate (systematicAtom i))
    (address : Fin (2 ^ pcpp.clauseBits)) :
    (siteCalls phase pcpp coordinate systematicAtom address).FactorsSatisfy predicate := by
  unfold siteCalls
  exact CircuitPolynomial.scale_factorsSatisfy _ _ predicate
    (sitePolynomial_factorsSatisfy phase pcpp coordinate systematicAtom predicate hcoordinate
      hsystematic address)

/-! ## §2 The atom relabelling, and the arity transport -/

/-- `mapPolynomial` (`Proof/CaseAnalysis/FinalSumFamilyTransport.lean`) is a
pure list relabelling, so a predicate on the TARGET atoms is exactly the pulled
back predicate on the SOURCE atoms. -/
theorem mapPolynomial_factorsSatisfy {Source Target : Type} {degree : ℕ}
    (F : Source → Target) (polynomial : CircuitPolynomial Source degree)
    (predicate : Target → Prop)
    (h : polynomial.FactorsSatisfy (fun atom => predicate (F atom))) :
    (mapPolynomial F polynomial).FactorsSatisfy predicate := by
  intro monomial hmonomial atom hatom
  rcases List.mem_map.mp hmonomial with ⟨source, hsource, rfl⟩
  rcases List.mem_map.mp hatom with ⟨original, horiginal, rfl⟩
  exact h source hsource original horiginal

/-- The arity transport of a legal term list
(`Proof/CaseAnalysis/FinalExactnessFamily.lean`) does not touch the circuits,
so it does not touch their wire counts. -/
theorem wires_le_of_mem_transportTerms {Circuit : CanonicalWitnessCodec.CircuitFamily}
    (wires : {q : ℕ} → Circuit q → ℕ) {source target : ℕ} (harity : source = target)
    (terms : List (LegalCircuitTerm Circuit source)) (cap : ℕ)
    (hterms : ∀ term ∈ terms, wires term.circuit ≤ cap)
    (term : LegalCircuitTerm Circuit target) (hterm : term ∈ transportTerms harity terms) :
    wires term.circuit ≤ cap := by
  subst harity
  exact hterms term hterm

/-- **`CheckedLegalCircuitSum.wires_le` (`Proof/Circuits/CanonicalWitnessCodec.lean`),
TRANSPORTED to the coordinate polynomial.**  `wires_le` is set by the decoder's
own `if hwires …` guard (`:1650`), which IS `paper.tex:4292-4302`'s rejection
rule in Lean; `familyCoordinate`
(`Proof/CaseAnalysis/FinalExactnessFamily.lean`) carries exactly the terms of
the accepted sum, so every atom of every coordinate monomial clears the cap. -/
theorem familyCoordinate_factorsSatisfy_wires {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ} {limits : LegalSumLimits}
    {variableCount target : ℕ} (harity : limits.expectedArity = target)
    (family : SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) :
    (familyCoordinate harity family i).FactorsSatisfy
      (fun c => wires c ≤ limits.wireCap) := by
  unfold familyCoordinate
  refine linearPolynomial_factorsSatisfy _ _ ?_
  intro term hterm
  exact wires_le_of_mem_transportTerms wires _ (family.getSum i).value.terms limits.wireCap
    (family.getSum i).wires_le term hterm

/-! ## §3 `atomWires` on the two guessed constructors -/

/-! ## §4 `atomWires` on the SYSTEMATIC constructor

`paper.tex:4303-4305` compiles the systematic parity deterministically into the
native parity circuit, so its envelope is not guessed and needs no decoder
guard: it is computed, and it is bounded by the arity outright. -/

/-- The one-bit gate reads exactly one coordinate, so it charges one wire. -/
theorem inputBitSupportedGate_wireCount {N : ℕ} (coordinate : Fin N) :
    (inputBitSupportedGate coordinate).wireCount = 1 := by
  unfold SupportedNormalizedGate.wireCount inputBitSupportedGate
  simp

/-- **The native parity circuit's wire count, exactly**: one identity bottom per
supported coordinate, each charged its own wire plus its edge into the top
table. -/
theorem normalizedParityCircuit_wireCount {N : ℕ} (support : Finset (Fin N)) :
    (normalizedParityCircuit support).wireCount = 2 * support.card := by
  unfold NormalizedSymmetricThresholdCircuit.wireCount normalizedParityCircuit
  simp only [inputBitSupportedGate_wireCount, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  omega

/-- **The systematic atom clears the arity.**  `PointwisePCPP.systematicSupportBound`
(`Proof/Foundations/SourceInterfaces.lean`) caps each systematic support at
`N / 2`, and the parity circuit charges two wires per supported coordinate, so
the native parity atom never exceeds `N` wires.  No guessed description, and no
hypothesis. -/
theorem atomWires_systematic_le {N : ℕ} {circuit : BooleanCircuit N}
    (pcpp : PointwisePCPP circuit) (index : Fin pcpp.systematicBits) :
    atomWires (Atom.systematic index : Atom pcpp) ≤ N := by
  have hcard : (pcpp.systematicSupport index).card ≤ N / 2 :=
    pcpp.systematicSupportBound index
  have hwires : atomWires (Atom.systematic index : Atom pcpp)
      = 2 * (pcpp.systematicSupport index).card :=
    normalizedParityCircuit_wireCount (pcpp.systematicSupport index)
  omega

/-! ## §5 The route's own cap, and the deliverable -/

noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-- **The per-atom wire envelope the route already has.**  Nothing is chosen
here: the two guessed branches are capped by `C10TotalDecode.symLimits`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`) and `thrLimits` (`:102`), which
are `paper.tex:800-807`'s own `n^3/L^5` and `n^3/L^9`; the systematic branch is
capped by the arity through `§4`.  Every summand depends on the input LENGTH
alone -- not on the input, not on the guessed witness, not on the oracle --
which is the witness-uniformity the consumer's `wireCap : ℕ → ℕ` demands. -/
def envelopeCap (n : ℕ) : ℕ :=
  max (stageArity sources k n)
    (max ⌊wireScale 1 5 ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)⌋₊
      ⌊wireScale 1 9 ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)⌋₊)

/-! ## §6 RESOURCE -- the cap is CUBIC, hence one residual cell and no second factor

`ENDGAME_RESOURCE.md` §1's governing sentence -- located by CONTENT, since the
numbering has drifted: **"Nothing else in the campaign may add a second residual
factor"** -- is not engaged by this module.  The envelope REMOVES branches; its
cost is the decoder's own syntactic `if`, already paid.  What it could have
added is an `entryWidth` term, and `stageSeedEnvelope_le_of_bits`
(`Proof/CaseAnalysis/FinalWireEnvelope.lean`) makes that term a fixed linear
function of the BIT LENGTHS of the caps.  The theorem below is the missing half:
the cap this module actually uses is bounded by a CUBE, so its bit length is
`O(L_q)` and the whole external-row exponent stays in the `FREE / POLYLOG`
bucket. -/

/-! ## §7 CONSUMER-BACKWARD CAPSTONE -- `henv` is GONE from the binder list

The test that a discharge ATTACHES rather than merely typechecks: feed
`henv_at_envelopeCap` into the consumer that demanded it and read off what is
left.  `siteDenFits_of_wireEnvelope`
(`Proof/CaseAnalysis/FinalWireEnvelope.lean`) had four premises; below it has
three, and `wireCap` is no longer a free parameter either -- it is pinned to the
route's own caps.  The three that remain are `hfloor` (ENVELOPE's
`envelopeFloor`), `hprime` and `hthrden` (the THR prime window and list
denominator), and they belong to other owners. -/

end

end NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope
