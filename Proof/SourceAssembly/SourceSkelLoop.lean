import Proof.SourceAssembly.SourceSkelSelect

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- Plain iteration `a0, f a0 0, f (f a0 0) 1, …` (every step definitional). -/
def seqOf {α : Type} (f : α → Nat → α) (a0 : α) : Nat → α
  | 0 => a0
  | j+1 => f (seqOf f a0 j) j

/-- **One clause's facts** at clause-start bank `(A, H)` with exit `(After, Hn)`, for the per-call values `values`:
the three per-clause interfaces, the phase list and uniformity, and the next clause's start invariant. -/
structure ClauseFacts (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (H Hn : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A After : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (siteFuel : Nat)
    (values : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes)
    (Inv : Nat → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Prop)
    (E : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List Stream.Entry) (liveScale : Nat) : Prop where
  trace : RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
    site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph ci H Hn A After (C10PartsSchedule.entryWidthSchedule sources k r n) siteFuel (code ph) values
  exit : SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
    site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph ci H Hn A After (C10PartsSchedule.entryWidthSchedule sources k r n) siteFuel (code ph) values
  append : SourceClauseAppend mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
    site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph ci H Hn A After (C10PartsSchedule.entryWidthSchedule sources k r n) siteFuel (code ph) values
  hentries : values.entries = E ci
  hprefix : values.phasePrefix = prefixEntries E ci.val
  hL : values.L = liveScale
  hT : values.target = (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
  next : Inv (ci.val+1) (install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) After (CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (ci.val+1))) Hn

/-- **One phase's per-clause steps** (THE PER-CLAUSE HOLE): fixed functions giving each clause's per-call values, exit
bank and exit heads from its start bank, a fixed entry list, one live scale, and the facts at every invariant bank. -/
structure ClauseSteps (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (ph : Phase) (siteFuel : Nat) (Inv : Nat → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Prop) where
  vals : (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) →
    RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes
  after : (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Nat → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
  hnext : (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Nat → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
  E : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List Stream.Entry
  liveScale : Nat
  facts : ∀ (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat), Inv ci.val A H →
    ClauseFacts mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci H (hnext A H ci.val) A (after A H ci.val) siteFuel (vals A H ci) Inv E liveScale

section build
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states} {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {ph : Phase} {siteFuel : Nat} {Inv : Nat → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Prop}

/-- The iterated clause chain from `(A0, H0)`. -/
def chainOf (St : ClauseSteps mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph siteFuel Inv) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) :
    Nat → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) × (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) :=
  seqOf (fun s j => (install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) (St.after s.1 s.2 j) (CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (j+1)), St.hnext s.1 s.2 j)) (A0, H0)

/-- One chain step, as an equation (proved by the recursion equations, never by `whnf`). -/
theorem chainOf_succ (St : ClauseSteps mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph siteFuel Inv) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (j : Nat) :
    chainOf St A0 H0 (j+1) = (install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) (St.after (chainOf St A0 H0 j).1 (chainOf St A0 H0 j).2 j) (CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (j+1)),
      St.hnext (chainOf St A0 H0 j).1 (chainOf St A0 H0 j).2 j) := by
  simp only [chainOf, seqOf]

/-- The invariant holds along the chain up to the last clause. -/
theorem chain_inv (St : ClauseSteps mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph siteFuel Inv) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (h0 : Inv 0 A0 H0) :
    ∀ j, j ≤ (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → Inv j (chainOf St A0 H0 j).1 (chainOf St A0 H0 j).2 := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    simp only [chainOf_succ]
    exact (St.facts ⟨j, Nat.lt_of_succ_le hj⟩ (chainOf St A0 H0 j).1 (chainOf St A0 H0 j).2 (ih (Nat.le_of_succ_le hj))).next

/-- The clause facts at the chain's own banks. -/
theorem facts_at (St : ClauseSteps mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph siteFuel Inv) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (h0 : Inv 0 A0 H0) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) :
    ClauseFacts mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci (chainOf St A0 H0 ci.val).2 (chainOf St A0 H0 (ci.val+1)).2 (chainOf St A0 H0 ci.val).1
      (St.after (chainOf St A0 H0 ci.val).1 (chainOf St A0 H0 ci.val).2 ci.val) siteFuel
      (St.vals (chainOf St A0 H0 ci.val).1 (chainOf St A0 H0 ci.val).2 ci) Inv St.E St.liveScale := by
  simp only [chainOf_succ]
  exact St.facts ci _ _ (chain_inv St A0 H0 h0 ci.val (Nat.le_of_lt ci.isLt))

/-- **The `ClauseLoop` from per-clause steps.** -/
def loopOfSteps (St : ClauseSteps mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph siteFuel Inv) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (h0 : Inv 0 A0 H0) :
    ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph (C10PartsSchedule.entryWidthSchedule sources k r n) (code ph) where
  H := fun j => (chainOf St A0 H0 j).2
  A := fun j => (chainOf St A0 H0 j).1
  s_after := fun j => St.after (chainOf St A0 H0 j).1 (chainOf St A0 H0 j).2 j
  siteFuel := siteFuel
  values := fun ci => St.vals (chainOf St A0 H0 ci.val).1 (chainOf St A0 H0 ci.val).2 ci
  trace := fun ci => (facts_at St A0 H0 h0 ci).trace
  exits := fun ci => (facts_at St A0 H0 h0 ci).exit
  appends := fun ci => (facts_at St A0 H0 h0 ci).append
  s_next := fun j _ => by simp only [chainOf_succ]
  hprefix := fun ci => by
    have hE : (fun c => (St.vals (chainOf St A0 H0 c.val).1 (chainOf St A0 H0 c.val).2 c).entries) = St.E :=
      funext fun c => (facts_at St A0 H0 h0 c).hentries
    rw [hE]
    exact (facts_at St A0 H0 h0 ci).hprefix

/-- **`LoopOut` from per-clause steps** (at site fuel `siteFuel`, exit invariant `Inv NC`). -/
def loopOutOfSteps (St : ClauseSteps mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph siteFuel Inv) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (h0 : Inv 0 A0 H0) :
    LoopOut mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph siteFuel A0 H0 (Inv (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) where
  L := loopOfSteps St A0 H0 h0
  hA0 := rfl
  hH0 := rfl
  liveScale := St.liveScale
  hL := fun ci => (facts_at St A0 H0 h0 ci).hL
  hT := fun ci => (facts_at St A0 H0 h0 ci).hT
  hsf := le_refl _
  hexit := chain_inv St A0 H0 h0 (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (le_refl _)

end build

end
end NearCubicWires.SourceSkeleton
end
