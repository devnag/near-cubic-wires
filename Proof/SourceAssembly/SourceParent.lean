import Proof.SourceAssembly.SourceParentPhase
import Proof.SourceAssembly.SourceBundle

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- A run's exit is determined by its machine, fuel and entry. -/
theorem exit_unique {u s n : ℕ} {q : Machine u s} {hin : Fin u → ℕ} {tin : Fin u → List Bool}
    {h1 h2 : Fin u → ℕ} {t1 t2 : Fin u → List Bool}
    (a : Step q n hin tin h1 t1) (b : Step q n hin tin h2 t2) : h1 = h2 ∧ t1 = t2 := by
  obtain ⟨r1, hr1, hh1, ht1, _⟩ := a
  obtain ⟨r2, hr2, hh2, ht2, _⟩ := b
  rw [hr1] at hr2
  cases Option.some.inj hr2
  exact ⟨hh1.symm.trans hh2, ht1.symm.trans ht2⟩

/-- The body tape carrying tail slot `i`. -/
abbrev Tl (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) (i : Fin 475) :=
  PCJda54a286946142d3_BranchPhases.body sources p k r scratch
    (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r)
      (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
      (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
      (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) i)

/-! ## `SelectedWitness`: what one `MaskedSelected` still owes -/

structure SelectedWitness (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (remainingFuel : Nat) (width : Phase → Nat)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) where
  cost : Phase → Nat
  /-- The explicit exit bank of each phase (the next phase's entry). -/
  exitH : Phase → Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat
  exitA : Phase → Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool
  /-- The three phases, each at its explicit entry. -/
  penalty : PhaseWitness mask selector packets rows compiler sources p k den r scratch
    (PolynomialClock.ordinaryClock k) n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
    (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty
    (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch)
    (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp)
    (cost .penalty) (width .penalty) (code .penalty)
  moment : PhaseWitness mask selector packets rows compiler sources p k den r scratch
    (PolynomialClock.ordinaryClock k) n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
    (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment
    (exitH .penalty) (exitA .penalty) (cost .moment) (width .moment) (code .moment)
  clause : PhaseWitness mask selector packets rows compiler sources p k den r scratch
    (PolynomialClock.ordinaryClock k) n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
    (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause
    (exitH .moment) (exitA .moment) (cost .clause) (width .clause) (code .clause)
  /-- Chaining: each phase machine, at the phase's cost, reaches the explicit exit. -/
  penaltyRun : Step (PCJda54a286946142d3_BranchPhases.phase sources p k r scratch site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty).2
    (cost .penalty) (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch)
    (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp)
    (exitH .penalty) (exitA .penalty)
  momentRun : Step (PCJda54a286946142d3_BranchPhases.phase sources p k r scratch site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment).2
    (cost .moment) (exitH .penalty) (exitA .penalty) (exitH .moment) (exitA .moment)
  clauseRun : Step (PCJda54a286946142d3_BranchPhases.phase sources p k r scratch site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause).2
    (cost .clause) (exitH .moment) (exitA .moment) (exitH .clause) (exitA .clause)
  /-- The later phases leave the earlier phases' record ports alone. -/
  penaltyKept : exitA .clause (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch .penalty) =
    exitA .penalty (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch .penalty)
  momentKept : exitA .clause (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch .moment) =
    exitA .moment (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch .moment)
  /-- The consumer's final conjuncts, on the clause phase's explicit exit. -/
  threshold : ∀ ph, C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤ width ph
  head : ∀ i, exitH .clause (Tl sources p k r scratch i) = 0
  words : ∀ ph j, exitA .clause (Tl sources p k r scratch (C10TailSlotsUniform.widthSlotT ph j)) =
    C10BodyWidths.widthWord (width ph) j
  blank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val →
    exitA .clause (Tl sources p k r scratch i) = []
  fits : PCJ374c44bb8b7f47d9_.branchFuel cost width + 2 ≤ remainingFuel

/-- **The plumbing at the selected level.** Every conjunct of `MaskedSelected`, from a
`SelectedWitness`: the chosen `realize` exits are identified with the explicit ones by
`exit_unique`, and the kept records by `Realizes.hencoded`. -/
theorem SelectedWitness.selected {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {tables : TableCertificate} {semantics : Certificate} {buildSource : SourceBuilder}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {remainingFuel : Nat} {width : Phase → Nat}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (w : SelectedWitness mask selector packets rows compiler sources p den hden k r scratch n x bits hp
      site remainingFuel width code) :
    MaskedSelected mask selector packets rows compiler tables semantics buildSource sources p den hden
      k r scratch n x bits hp site remainingFuel width := by
  have pS := w.penalty.spec
  let P := maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p
    k den r scratch (PolynomialClock.ordinaryClock k) n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
    (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty
    (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch)
    (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp)
    (w.cost .penalty) (width .penalty) pS
  have hP := exit_unique P.realize.run w.penaltyRun
  have mS : MaskedPhase mask selector packets rows compiler sources p k den r scratch
      (PolynomialClock.ordinaryClock k) n x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment
      P.realize.heads P.realize.exit (w.cost .moment) (width .moment) := by
    rw [hP.1, hP.2]
    exact w.moment.spec
  let M := maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p
    k den r scratch (PolynomialClock.ordinaryClock k) n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
    (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment
    P.realize.heads P.realize.exit (w.cost .moment) (width .moment) mS
  have mRun : Step (PCJda54a286946142d3_BranchPhases.phase sources p k r scratch site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment).2
      (w.cost .moment) P.realize.heads P.realize.exit (w.exitH .moment) (w.exitA .moment) := by
    rw [hP.1, hP.2]
    exact w.momentRun
  have hM := exit_unique M.realize.run mRun
  have cS : MaskedPhase mask selector packets rows compiler sources p k den r scratch
      (PolynomialClock.ordinaryClock k) n x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause
      M.realize.heads M.realize.exit (w.cost .clause) (width .clause) := by
    rw [hM.1, hM.2]
    exact w.clause.spec
  let Cl := maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p
    k den r scratch (PolynomialClock.ordinaryClock k) n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
    (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause
    M.realize.heads M.realize.exit (w.cost .clause) (width .clause) cS
  have cRun : Step (PCJda54a286946142d3_BranchPhases.phase sources p k r scratch site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause).2
      (w.cost .clause) M.realize.heads M.realize.exit (w.exitH .clause) (w.exitA .clause) := by
    rw [hM.1, hM.2]
    exact w.clauseRun
  have hC := exit_unique Cl.realize.run cRun
  refine ⟨w.cost, pS, mS, cS, ?_, ?_, w.threshold, ?_, ?_, ?_, w.fits⟩
  · rw [hC.2, w.penaltyKept, ← hP.2]
    exact P.realize.hencoded
  · rw [hC.2, w.momentKept, ← hM.2]
    exact M.realize.hencoded
  · rw [hC.1]
    exact w.head
  · rw [hC.2]
    exact w.words
  · rw [hC.2]
    exact w.blank

/-! ## `SourceContract`: the `Choices` and a witness at every admitted instance -/

/-- The site machine that a fixed `SourceCode` determines: `SourceTrace._hcode`'s left side. -/
def siteOfCode {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma} {k r scratch : Nat}
    {ph : Phase} (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) :
    Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states :=
  ⟨_, RecoveryFocus.machine code.whole
    (Composition.machine (PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code code.firstCode.base.cached))
      (CloseoutRowsDegreeLoop.machine
        (Composition.machine
          (Composition.machine (RecoveryFocus.machine code.slots (f_machine code.a))
            (Composition.machine (RecoveryFocus.machine code.enc e_machine)
              (RecoveryFocus.machine code.app CloseoutFinalC10SingleAppend.machine)))
          (PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code code.refillCode.base.cached)))))⟩

/-- `SourceTrace._hcode` is `rfl` once `site` is defined from the code. -/
theorem hcode_of_siteOfCode {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma} {k r scratch : Nat}
    {ph : Phase} (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) :
    (⟨_, RecoveryFocus.machine code.whole
      (Composition.machine (PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code code.firstCode.base.cached))
        (CloseoutRowsDegreeLoop.machine
          (Composition.machine
            (Composition.machine (RecoveryFocus.machine code.slots (f_machine code.a))
              (Composition.machine (RecoveryFocus.machine code.enc e_machine)
                (RecoveryFocus.machine code.app CloseoutFinalC10SingleAppend.machine)))
            (PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code code.refillCode.base.cached)))))⟩ :
      Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states) =
    siteOfCode code := rfl

/-- The hierarchy index the `Choices` fix. -/
abbrev kOf (capIndex remainingDegree : (sources : EightSources) → (gamma : Real) → 0 < gamma →
      gamma < 1/2 → Parameters sources gamma → Nat)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : Nat :=
  ControllerCappedRuntime.hierarchyIndex sources p (capIndex sources gamma hg hh p+1)
    (remainingDegree sources gamma hg hh p)

/-- The numeric and schedule `Choices` (everything but the site machine). -/
structure SourceChoices where
  capIndex : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingDegree : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  r : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  base : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  scratch : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingFuel : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat → Nat
  widths : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    (p : Parameters sources gamma) → (n : Nat) → BitInput n → List Bool → Phase → Nat
  remainingCoefficient : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingOnset : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  tableCoefficient : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  tableDegree : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat

/-- ONE shared per-clause code per `(mode, phase)`, fixed before `n x bits`
(`paper.tex:4280-4290`); the site machine is DEFINED from it (`siteOfCode`). -/
abbrev CodeFamily (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (ch : SourceChoices) :=
  (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) →
    (p : Parameters sources gamma) → Bool → (ph : Phase) →
    RCFive.Source.SourceCode mask selector packets rows sources p
      (kOf ch.capIndex ch.remainingDegree sources gamma hg hh p) (ch.r sources gamma hg hh p)
      (ch.scratch sources gamma hg hh p) ph

/-- The site family a code family determines. -/
abbrev CodeFamily.site {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {ch : SourceChoices}
    (code : CodeFamily mask selector packets rows ch)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) (mode : Bool) (ph : Phase) :
    Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p
      (kOf ch.capIndex ch.remainingDegree sources gamma hg hh p) (ch.r sources gamma hg hh p)
      (ch.scratch sources gamma hg hh p)) states :=
  siteOfCode (code sources gamma hg hh p mode ph)

/-- The `Choices` of `SourceBundle` that `(ch, code)` determine. -/
def choicesOf {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} (ch : SourceChoices)
    (code : CodeFamily mask selector packets rows ch) : PCJ6e421fabe2aa4155_SourceBundle.Choices :=
  ⟨ch.capIndex, ch.remainingDegree, ch.r, ch.base, ch.scratch, code.site,
    ch.remainingFuel, ch.widths, ch.remainingCoefficient, ch.remainingOnset, ch.tableCoefficient,
    ch.tableDegree⟩

/-- **What is owed below `MaskedSelected`:** a `SelectedWitness` at every admitted instance,
for the `Choices` `choicesOf ch code`. -/
def SourceObligations (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (ch : SourceChoices) (code : CodeFamily mask selector packets rows ch) : Type :=
  (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) →
    (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) →
    let C := ControllerCappedRuntime.continuation sources p (ch.capIndex sources gamma hg hh p+1)
      (ch.remainingDegree sources gamma hg hh p) (ch.r sources gamma hg hh p)
      (ch.base sources gamma hg hh p) (ch.scratch sources gamma hg hh p)
      (code.site sources gamma hg hh p) (ch.remainingFuel sources gamma hg hh p)
    (hn : (ControllerCappedSelected.workerData sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData (ch.capIndex sources gamma hg hh p+1) C)).onset ≤ n) →
    (hp : (ControllerCappedSelected.workerData sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData (ch.capIndex sources gamma hg hh p+1) C)).passed n x bits = true) →
    SelectedWitness mask selector packets rows compiler sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p)) C.k
      (ch.r sources gamma hg hh p) (ch.scratch sources gamma hg hh p) n x bits hp
      (code.site sources gamma hg hh p)
      (ch.remainingFuel sources gamma hg hh p n) (ch.widths sources gamma hg hh p n x bits)
      (fun ph => code sources gamma hg hh p
        (PCJ374c44bb8b7f47d9_.S.mode sources p (ch.capIndex sources gamma hg hh p+1)
          (Nat.succ_pos (ch.capIndex sources gamma hg hh p)) C.k
          (ch.r sources gamma hg hh p) (ch.scratch sources gamma hg hh p) n x bits hp) ph)

/-- **The source contract**: the schedule choices, the shared code family, and the owed
witnesses. Everything below `MaskedSelected` that is still open is inside this type. -/
def SourceContract (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws) : Type :=
  Σ (ch : SourceChoices) (code : CodeFamily mask selector packets rows ch),
    SourceObligations mask selector packets rows compiler ch code

/-- The `Choices` a contract determines. -/
def SourceContract.choices {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    (c : SourceContract mask selector packets rows compiler) :
    PCJ6e421fabe2aa4155_SourceBundle.Choices :=
  choicesOf c.1 c.2.1

/-- **The conditional parent.** A contract gives `SourceBundle.Physical` at its own `Choices`,
for ANY `tables`, `semantics`, `buildSource` (they are only passed through). -/
theorem physical_of_contract {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (c : SourceContract mask selector packets rows compiler) :
    PCJ6e421fabe2aa4155_SourceBundle.Physical mask selector packets rows compiler tables semantics
      buildSource c.choices := by
  intro sources gamma hg hh p n x bits C hn hp
  refine SelectedWitness.selected (code := fun ph => c.2.1 sources gamma hg hh p
    (PCJ374c44bb8b7f47d9_.S.mode sources p (c.1.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (c.1.capIndex sources gamma hg hh p)) C.k
      (c.1.r sources gamma hg hh p) (c.1.scratch sources gamma hg hh p) n x bits hp) ph) ?_
  exact c.2.2 sources gamma hg hh p n x bits hn hp

end
end NearCubicWires.SourceParent
end
