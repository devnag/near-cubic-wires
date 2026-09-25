import Proof.SourceAssembly.SourcePhaseChain

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourcePhase
open NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- **The per-clause family of one phase.** -/
structure ClauseLoop (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (bits : List Bool)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (mode : Bool) (ph : Phase) (b : Nat)
    (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) where
  H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat
  A : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool
  s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool
  siteFuel : Nat
  values : ∀ ci : Fin (NC sources k clock x oracle),
    RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code
  trace : ∀ ci : Fin (NC sources k clock x oracle),
    RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci)
  exits : ∀ ci : Fin (NC sources k clock x oracle),
    SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci)
  appends : ∀ ci : Fin (NC sources k clock x oracle),
    SourceClauseAppend mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci)
  s_next : ∀ (j : Nat), j < NC sources k clock x oracle →
    A (j+1) = install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode) (s_after j)
      (CD sources k clock x oracle (j+1))
  hprefix : ∀ ci : Fin (NC sources k clock x oracle),
    (values ci).phasePrefix = prefixEntries (fun c => (values c).entries) ci.val

/-- The phase's record stream: the clause-ordered concatenation of the clauses' entries. -/
abbrev ClauseLoop.entries {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {b : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph b code) :
    List Stream.Entry :=
  (List.ofFn (fun c => (L.values c).entries)).flatten

/-- **`PhaseWitness` from its loop** — every E field produced, the rest passed through. -/
def PhaseWitness.ofLoop {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase}
    {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat}
    {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool}
    {fuel width : Nat} {b : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph b code)
    -- rows D1–D7: the phase records
    (liveScale target : Nat) (limits : CanonicalWitnessCodec.LegalSumLimits) (denBits : Nat)
    (order : List (CircuitMonomial (C10TotalDecode.Atom (pcppAt sources k clock x oracle)) 4))
    (horder : (Poly sources p k den clock n x oracle bits ph).monomials.Perm order)
    (hmode : ∀ m ∈ order, ∀ atom ∈ m.factors, C10NaturalModeAtoms.ModeAtom mode atom)
    (hrecords : List.Forall₂ (fun m e =>
      e.coefficient = CloseoutFinalC10SupplierCalls.coefficientEstimate m.coefficient ∧
      e.count = (LiveRows.fraction sources liveScale target mode m.factors).1 ∧
      e.denominator = (LiveRows.fraction sources liveScale target mode m.factors).2) order L.entries)
    (hmass : (Poly sources p k den clock n x oracle bits ph).coefficientMass ≤
      C10FamilyMass.siteMassBound limits.coefficientMassCap ph)
    (hcoeff : CloseoutFinalC10SupplierCalls.CoefficientsFit b (Poly sources p k den clock n x oracle bits ph))
    (htarget : C10SupplierAccuracyChain.accuracyTarget (constantsOf sources) limits ph ≤ target)
    (htargetpos : 0 < target)
    (hden : ∀ m ∈ order, (LiveRows.fraction sources liveScale target mode m.factors).2 ≤ 2^denBits)
    (hdenwidth : denBits+1 ≤ b)
    -- rows C1–C4: the phase entry
    (entryFuel : Nat)
    (middleH : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat)
    (middle : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool)
    (hentry : Step (RecoveryFocus.machine (PCJda54a286946142d3_BranchPhases.body sources p k r scratch)
      (PCJda54a286946142d3_BranchPhases.phaseEntry sources p k r scratch mode ph).2) entryFuel hin tin middleH middle)
    (hhead : ∀ i, middleH (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i) = L.H 0 i)
    (htape : ∀ i, middle (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i) = L.A 0 i)
    (hdriver : middleH (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = 1)
    (hword : middle (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) =
      UnaryTemplate.tape (NC sources k clock x oracle))
    -- the loop-start facts (from the entry)
    (e_blank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 →
      L.A 0 (Wd sources p k r scratch ph i) = [])
    (e_fresh : ∀ i : Fin 278, 219 ≤ i.val → L.A 0 (Wd sources p k r scratch ph i) = [])
    (e_record : L.A 0 (Fd sources p k r scratch ph 215) = [])
    (e_log : L.A 0 (Fd sources p k r scratch ph 218) = [])
    (e_driver : L.A 0 (Wd sources p k r scratch ph 218) = List.replicate b true)
    (e_stream : L.A 0 (Wd sources p k r scratch ph 81) = [])
    (e_count : L.A 0 (Wd sources p k r scratch ph 90) = CompareMachine.word 0)
    (e_cacheH : ∀ i, L.H 0 (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0)
    (e_termH : L.H 0 (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) = 0)
    (e_countT : L.A 0 (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) =
      List.replicate (NC sources k clock x oracle) true)
    (e_cached : ∀ i, L.A 0 (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) =
      CD sources k clock x oracle 0 i)
    (e_Hw : ∀ i, L.H 0 (Wd sources p k r scratch ph i) = 0)
    (e_Hf : ∀ i, L.H 0 (Fd sources p k r scratch ph i) = 0)
    -- cost and the consumer's fuel/width equations
    (cost : Nat)
    (hcost : 4*NC sources k clock x oracle+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
      ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)+L.siteFuel+21 ≤ cost)
    (hfuel : fuel = entryFuel+1+(NC sources k clock x oracle*(cost+3)+3+1+
      CloseoutFinalC10RetainedPhaseFold.fuel b L.entries.length))
    (hwidth : width = CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width b) L.entries) :
    PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code :=
  have hN : NC sources k clock x oracle = 2^(pcppAt sources k clock x oracle).clauseBits := rfl
  have E4 := fields_E4 L.H L.A L.s_after L.values L.exits L.s_next (NC sources k clock x oracle) hN
    e_blank e_fresh e_record e_log
  have E3 := fields_E3 L.H L.A L.s_after L.values L.appends L.s_next L.hprefix
    (NC sources k clock x oracle) hN e_stream e_count
  have E1 := fields_E1 L.H L.A L.s_after L.values L.exits (NC sources k clock x oracle) hN e_cacheH e_Hw e_Hf
  have E5 := fields_E5 L.H L.A L.s_after L.values L.exits L.s_next e_cacheH e_termH e_countT e_cached
  { liveScale := liveScale
    target := target
    limits := limits
    denBits := denBits
    order := order
    b := b
    entries := L.entries
    H := L.H
    A := L.A
    entryFuel := entryFuel
    N := NC sources k clock x oracle
    cost := cost
    middleH := middleH
    middle := middle
    siteFuel := L.siteFuel
    s_after := L.s_after
    horder := horder
    hmode := hmode
    hrecords := hrecords
    hmass := hmass
    hcoeff := hcoeff
    htarget := htarget
    htargetpos := htargetpos
    hden := hden
    hdenwidth := hdenwidth
    hHw := E1.1
    hHf := E1.2
    hwidthDriver := field_E2 L.H L.A L.s_after L.values L.exits L.s_next (NC sources k clock x oracle) hN b e_driver
    hcount := E3.1
    hstream := E3.2
    hblank := E4.1
    hfresh := E4.2.1
    hrecord := E4.2.2.1
    hlog := E4.2.2.2
    hentry := hentry
    hhead := hhead
    htape := htape
    hdriver := hdriver
    hword := hword
    hN := hN
    hcost := hcost
    s_head := E5.1
    s_terminal_head := E5.2.1
    s_count := E5.2.2.1
    s_cached := E5.2.2.2
    values := L.values
    trace := L.trace
    s_restored := field_E6 L.H L.A L.s_after L.values L.exits
    s_next := L.s_next
    hfuel := hfuel
    hwidth := hwidth }

end
end NearCubicWires.SourcePhase
end
