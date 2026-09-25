import Proof.CaseAnalysis.FiveSourceTrace

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

/-! ## Names for the consumer's `let`s (reducible, so they unfold to its terms) -/

abbrev Poly (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k den : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (bits : List Bool) (ph : Phase) :=
  CloseoutFinalC10Exactness.phasePolynomial ph (pcppAt sources k clock x oracle)
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits)
    (C10TotalDecode.Atom.systematic (pcpp := pcppAt sources k clock x oracle))

/-- Phase word bank `wordSlots ph` in the body layout. -/
abbrev Wd (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) (ph : Phase) :=
  CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
    (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) ph

/-- Phase fold bank `foldSlots ph` in the body layout. -/
abbrev Fd (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) (ph : Phase) :=
  CloseoutFinalC10RetainedPhaseFold.foldSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
    (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) ph

/-- The number of PCPP clause addresses of the actual request. -/
abbrev NC (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    {n : Nat} (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)) :=
  2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits

/-- The query-cache contents at clause `j` with EMPTY query word. -/
abbrev CD (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    {n : Nat} (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (j : Nat) :=
  PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle)
      ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)))
    (req sources k clock x oracle).arity j
    (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources)
      ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) []

/-! ## `PhaseWitness`: what one `MaskedPhase` still owes -/

structure PhaseWitness (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (bits : List Bool)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (mode : Bool) (ph : Phase)
    (hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat)
    (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool)
    (fuel width : Nat)
    (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) where
  /- data (the consumer's existential witnesses) -/
  liveScale : Nat
  target : Nat
  limits : CanonicalWitnessCodec.LegalSumLimits
  denBits : Nat
  order : List (CircuitMonomial (C10TotalDecode.Atom (pcppAt sources k clock x oracle)) 4)
  b : Nat
  entries : List Stream.Entry
  H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat
  A : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool
  entryFuel : Nat
  N : Nat
  cost : Nat
  middleH : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat
  middle : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool
  siteFuel : Nat
  s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool
  /- phase records: the expansion of `phasePolynomial ph` -/
  horder : (Poly sources p k den clock n x oracle bits ph).monomials.Perm order
  hmode : ∀ m ∈ order, ∀ atom ∈ m.factors, C10NaturalModeAtoms.ModeAtom mode atom
  hrecords : List.Forall₂ (fun m e =>
      e.coefficient = CloseoutFinalC10SupplierCalls.coefficientEstimate m.coefficient ∧
      e.count = (LiveRows.fraction sources liveScale target mode m.factors).1 ∧
      e.denominator = (LiveRows.fraction sources liveScale target mode m.factors).2)
    order entries
  hmass : (Poly sources p k den clock n x oracle bits ph).coefficientMass ≤
    C10FamilyMass.siteMassBound limits.coefficientMassCap ph
  hcoeff : CloseoutFinalC10SupplierCalls.CoefficientsFit b (Poly sources p k den clock n x oracle bits ph)
  htarget : C10SupplierAccuracyChain.accuracyTarget (constantsOf sources) limits ph ≤ target
  htargetpos : 0 < target
  hden : ∀ m ∈ order, (LiveRows.fraction sources liveScale target mode m.factors).2 ≤ 2^denBits
  hdenwidth : denBits+1 ≤ b
  /- the fold's entry requirements on the bank after the clause loop, `A N` -/
  hHw : ∀ i, H N (Wd sources p k r scratch ph i) = 0
  hHf : ∀ i, H N (Fd sources p k r scratch ph i) = 0
  hwidthDriver : A N (Wd sources p k r scratch ph 218) = List.replicate b true
  hcount : A N (Wd sources p k r scratch ph 90) = CompareMachine.word entries.length
  hstream : A N (Wd sources p k r scratch ph 81) = Stream.words b entries
  hblank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 →
    A N (Wd sources p k r scratch ph i) = []
  hfresh : ∀ i : Fin 278, 219 ≤ i.val → A N (Wd sources p k r scratch ph i) = []
  hrecord : A N (Fd sources p k r scratch ph 215) = []
  hlog : A N (Fd sources p k r scratch ph 218) = []
  /- the fixed accepted phase entry, from THIS phase's entry bank -/
  hentry : Step (RecoveryFocus.machine (PCJda54a286946142d3_BranchPhases.body sources p k r scratch)
      (PCJda54a286946142d3_BranchPhases.phaseEntry sources p k r scratch mode ph).2)
    entryFuel hin tin middleH middle
  hhead : ∀ i, middleH (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i) = H 0 i
  htape : ∀ i, middle (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i) = A 0 i
  hdriver : middleH (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = 1
  hword : middle (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = UnaryTemplate.tape N
  hN : N = 2^(pcppAt sources k clock x oracle).clauseBits
  hcost : 4*N+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
      ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)+siteFuel+21 ≤ cost
  /- clause-loop invariants -/
  s_head : ∀ (j : Nat), j ≤ NC sources k clock x oracle → ∀ (i : Fin 19),
    H j (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0
  s_terminal_head : ∀ (j : Nat), j < NC sources k clock x oracle →
    H j (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) = 0
  s_count : ∀ (j : Nat), j < NC sources k clock x oracle →
    A j (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) =
      List.replicate (NC sources k clock x oracle) true
  s_cached : ∀ (j : Nat), j < NC sources k clock x oracle → ∀ (i : Fin 19),
    A j (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = CD sources k clock x oracle j i
  /- THE PER-CLAUSE BOTTOM: one fixed code, per-clause values and traces -/
  values : ∀ ci : Fin (NC sources k clock x oracle),
    RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code
  trace : ∀ ci : Fin (NC sources k clock x oracle),
    RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci)
  /- cache restoration and the next clause's cache -/
  s_restored : ∀ (j : Nat), j < NC sources k clock x oracle → ∀ (i : Fin 19),
    s_after j (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = CD sources k clock x oracle j i
  s_next : ∀ (j : Nat), j < NC sources k clock x oracle →
    A (j+1) = install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode) (s_after j)
      (CD sources k clock x oracle (j+1))
  /- the phase's fuel and width, as the consumer defines them -/
  hfuel : fuel = entryFuel+1+(N*(cost+3)+3+1+CloseoutFinalC10RetainedPhaseFold.fuel b entries.length)
  hwidth : width = CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width b) entries

/-- **The plumbing.** A `PhaseWitness` is a `MaskedPhase`: its fields in order, with
`_s_source` produced at every clause by the existing `SourceTrace.toSpec`. -/
theorem PhaseWitness.spec {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector} {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase}
    {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat}
    {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool}
    {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :
    MaskedPhase mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width :=
  ⟨w.liveScale, w.target, w.limits, w.denBits, w.order, w.b, w.entries, w.H, w.A, w.entryFuel,
    w.N, w.cost, w.middleH, w.middle, w.horder, w.hmode, w.hrecords, w.hmass, w.hcoeff,
    w.htarget, w.htargetpos, w.hden, w.hdenwidth, w.hHw, w.hHf, w.hwidthDriver, w.hcount,
    w.hstream, w.hblank, w.hfresh, w.hrecord, w.hlog, w.hentry, w.hhead, w.htape, w.hdriver,
    w.hword, w.hN, w.siteFuel, w.hcost, w.s_after, w.s_head, w.s_terminal_head, w.s_count,
    w.s_cached,
    (fun ci => RCFive.Source.SourceTrace.toSpec mask selector packets rows compiler sources p k den
      r scratch clock n x oracle bits site mode ph ci (w.H ci.val) (w.H (ci.val+1)) (w.A ci.val)
      (w.s_after ci.val) w.b w.siteFuel code (w.values ci) (w.trace ci)),
    w.s_restored, w.s_next, w.hfuel, w.hwidth⟩

end
end NearCubicWires.SourceParent
end
