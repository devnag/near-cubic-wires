import Proof.SourceAssembly.SourcePhaseEntry

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

section run
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
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
    {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}

theorem site_step (tables : TableCertificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) (j : Nat) (hj : j < NC sources k clock x oracle) :
    Step (site mode ph).2 w.siteFuel (w.H j)
      (install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode) (w.A j)
        (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle)
          ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)))
          (req sources k clock x oracle).arity j
          (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources)
            ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity))
          (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauses ⟨j, hj⟩).left,
            literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauses ⟨j, hj⟩).right])))
      (w.H (j+1)) (w.s_after j) :=
  buildSource sources p k r scratch site mode ph (CloseoutLanguage.selectedPCPP sources)
    (req sources k clock x oracle) ⟨j, hj⟩ (w.H j) (w.H (j+1)) (w.A j) (w.s_after j) w.b w.siteFuel
    (PCJ9eff70d512234a4c_Fixed.sourceProjection selector compiler tables sources p k den r scratch clock n x oracle
      bits site mode ph ⟨j, hj⟩ (w.H j) (w.H (j+1)) (w.A j) (w.s_after j) w.b w.siteFuel
      (PCJ38fbfed565f64139_Physical.sourceProjection selector compiler sources p k den r scratch clock n x oracle
        bits site mode ph ⟨j, hj⟩ (w.H j) (w.H (j+1)) (w.A j) (w.s_after j) w.b w.siteFuel
        (PCJd4d1d9d7d1fa4313_Production.producedSourceProjection selector packets rows compiler sources p k den r
          scratch clock n x oracle bits site mode ph ⟨j, hj⟩ (w.H j) (w.H (j+1)) (w.A j) (w.s_after j) w.b w.siteFuel
          (PCJc4297ab269d8423a_Source.maskedSourceProjection mask selector packets rows compiler sources p k den r
            scratch clock n x oracle bits site mode ph ⟨j, hj⟩ (w.H j) (w.H (j+1)) (w.A j) (w.s_after j) w.b w.siteFuel
            (RCFive.Source.SourceTrace.toSpec mask selector packets rows compiler sources p k den r scratch clock n x
              oracle bits site mode ph ⟨j, hj⟩ (w.H j) (w.H (j+1)) (w.A j) (w.s_after j) w.b w.siteFuel code
              (w.values ⟨j, hj⟩) (w.trace ⟨j, hj⟩))))))

/-- The accepted `SiteLoop` of a `PhaseWitness`. -/
def siteLoop (tables : TableCertificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :
    PCJ30aa6f1b7c2a4221_.SiteLoop sources p k r scratch site mode ph (CloseoutLanguage.selectedPCPP sources)
      (req sources k clock x oracle) w.H w.A w.siteFuel where
  after := w.s_after
  head := w.s_head
  terminal_head := w.s_terminal_head
  count := w.s_count
  cached := w.s_cached
  site_run := fun j hj => site_step tables buildSource w j hj
  restored := w.s_restored
  next := w.s_next

/-- Every clause round at the phase's `cost` (`SiteLoop.rounds`, enlarged by `hcost`). -/
theorem rounds (tables : TableCertificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :
    ∀ j, j < w.N → Step (PCJda54a286946142d3_BranchPhases.clause sources p k r scratch site mode ph).2 w.cost
      (w.H j) (w.A j) (w.H (j+1)) (w.A (j+1)) := by
  intro j hj
  have hn : j < NC sources k clock x oracle := by
    have := w.hN
    simpa only [this, pcppAt] using hj
  have run := (siteLoop tables buildSource w).rounds sources p k r scratch site mode ph
    (CloseoutLanguage.selectedPCPP sources) (req sources k clock x oracle) w.H w.A w.siteFuel j hn
  apply run.enlarge
  have := w.hcost
  have hN := w.hN
  simpa only [hN, pcppAt] using this

/-- The loop exit heads (body at `H N`, driver at 1). -/
abbrev loopH (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :=
  dockH (PCJda54a286946142d3_BranchPhases.loops sources p k r scratch) w.middleH
    (Fin.addCases (w.H w.N) (fun _ : Fin 1 => 1))

/-- The loop exit bank (body at `A N`, driver at `tape N`). -/
abbrev loopA (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :=
  install (PCJda54a286946142d3_BranchPhases.loops sources p k r scratch) w.middle
    (Fin.addCases (w.A w.N) (fun _ : Fin 1 => UnaryTemplate.tape w.N))

theorem loops_inj :
    Function.Injective (PCJda54a286946142d3_BranchPhases.loops sources p k r scratch) :=
  WorkspaceSelectedEntryRepeat.slots_injective _ _ (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.body_ne_driver sources p k r scratch)

theorem loops_castAdd (i : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) :
    PCJda54a286946142d3_BranchPhases.loops sources p k r scratch (i.castAdd 1) =
      PCJda54a286946142d3_BranchPhases.body sources p k r scratch i := by
  simp [PCJda54a286946142d3_BranchPhases.loops, WorkspaceSelectedEntryRepeat.slots]

theorem loops_natAdd :
    PCJda54a286946142d3_BranchPhases.loops sources p k r scratch
        (Fin.natAdd (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (0 : Fin 1)) =
      PCJda54a286946142d3_BranchPhases.driver sources p k r scratch := by
  simp [PCJda54a286946142d3_BranchPhases.loops, WorkspaceSelectedEntryRepeat.slots]

theorem loopH_body (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) (i : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) :
    loopH w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i) = w.H w.N i := by
  have h := dockH_slot (PCJda54a286946142d3_BranchPhases.loops sources p k r scratch) loops_inj w.middleH
    (Fin.addCases (w.H w.N) (fun _ : Fin 1 => 1)) (i.castAdd 1)
  rw [loops_castAdd, Fin.addCases_left] at h
  exact h

theorem loopA_body (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) (i : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) :
    loopA w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i) = w.A w.N i := by
  have h := install_slot (PCJda54a286946142d3_BranchPhases.loops sources p k r scratch) loops_inj w.middle
    (Fin.addCases (w.A w.N) (fun _ : Fin 1 => UnaryTemplate.tape w.N)) (i.castAdd 1)
  rw [loops_castAdd, Fin.addCases_left] at h
  exact h

theorem loopH_driver (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :
    loopH w (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = 1 := by
  have h := dockH_slot (PCJda54a286946142d3_BranchPhases.loops sources p k r scratch) loops_inj w.middleH
    (Fin.addCases (w.H w.N) (fun _ : Fin 1 => 1)) (Fin.natAdd _ (0 : Fin 1))
  rw [loops_natAdd, Fin.addCases_right] at h
  exact h

theorem loopA_driver (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :
    loopA w (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = UnaryTemplate.tape w.N := by
  have h := install_slot (PCJda54a286946142d3_BranchPhases.loops sources p k r scratch) loops_inj w.middle
    (Fin.addCases (w.A w.N) (fun _ : Fin 1 => UnaryTemplate.tape w.N)) (Fin.natAdd _ (0 : Fin 1))
  rw [loops_natAdd, Fin.addCases_right] at h
  exact h

/-- The fold's exit facts on its output `out`, relative to the loop exit `A N`. -/
abbrev FoldOut (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code)
    (out : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) : Prop :=
  out (Fd sources p k r scratch ph 215) = Stream.recordWord
      (CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width w.b) w.entries)
      (CompetitorSumFold.folded CompetitorSumWidth.zero (Stream.contributions w.entries)) 1 1 ∧
  out (Wd sources p k r scratch ph 274) =
    List.replicate (CloseoutFinalC10WorkerDock.joinScalarWidth w.b w.entries.length) true ∧
  out (Wd sources p k r scratch ph 275) = List.replicate
    (CompetitorRationalDecision.width (CloseoutFinalC10WorkerDock.joinScalarWidth w.b w.entries.length)) true ∧
  (∀ i : Fin 218, i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217 →
    out (Fd sources p k r scratch ph (i.castAdd 1)) = w.A w.N (Fd sources p k r scratch ph (i.castAdd 1))) ∧
  (∀ i, (∀ j, Wd sources p k r scratch ph j ≠ i) → (∀ j, Fd sources p k r scratch ph j ≠ i) → out i = w.A w.N i)

/-- **J1, explicit.** The phase machine runs, at the consumer's phase fuel, from the phase's entry
bank to the loop exit with the fold's output installed on the body. -/
theorem phase_explicit (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :
    ∃ out, Step (PCJda54a286946142d3_BranchPhases.phase sources p k r scratch site mode ph).2 fuel hin tin
        (loopH w) (install (PCJda54a286946142d3_BranchPhases.body sources p k r scratch) (loopA w) out) ∧
      FoldOut w out := by
  have certified := semantics sources w.liveScale w.target mode ph
    (Poly sources p k den clock n x oracle bits ph) w.b w.denBits w.limits w.order w.entries w.horder w.hmode
    w.hrecords w.hmass w.hcoeff w.htarget w.htargetpos w.hden w.hdenwidth
  obtain ⟨_hfailure, _hpoint, _hbudget, _hcalls, hvalid⟩ := certified
  have hloop := WorkspaceSelectedEntryRepeat.run_at (PCJda54a286946142d3_BranchPhases.clause sources p k r scratch site mode ph).2
    (PCJda54a286946142d3_BranchPhases.body sources p k r scratch) (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.body_ne_driver sources p k r scratch)
    w.N w.cost w.H w.A w.middleH w.middle w.hhead w.htape w.hdriver w.hword (rounds tables buildSource w)
  obtain ⟨out, hstep, hrec, h274, h275, hprot, hframe⟩ :=
    CloseoutFinalC10RetainedPhaseFold.run (PCJda54a286946142d3_BranchPhases.offset sources p k r)
      (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
      (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
      (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) ph w.b w.entries (w.H w.N) (w.A w.N)
      hvalid w.hHw w.hHf w.hwidthDriver w.hcount w.hstream w.hblank w.hfresh w.hrecord w.hlog
  have hfold := hstep.dock (PCJda54a286946142d3_BranchPhases.body sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch) (loopH w) (loopA w)
    (loopH_body w) (loopA_body w)
  have hH : dockH (PCJda54a286946142d3_BranchPhases.body sources p k r scratch) (loopH w) (w.H w.N) = loopH w :=
    dockH_existing _ _ _ (loopH_body w)
  rw [hH] at hfold
  have whole := w.hentry.seq (hloop.seq hfold)
  rw [← w.hfuel] at whole
  exact ⟨out, whole, hrec, h274, h275, hprot, hframe⟩

/-- **J1, realized.** The chosen `realize` exit of the phase IS the explicit exit. -/
theorem realize_exit (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code) :
    let P := maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
      clock n x oracle bits site mode ph hin tin fuel width w.spec
    P.realize.heads = loopH w ∧
    ∃ out, P.realize.exit = install (PCJda54a286946142d3_BranchPhases.body sources p k r scratch) (loopA w) out ∧
      FoldOut w out := by
  intro P
  obtain ⟨out, hrun, hout⟩ := phase_explicit tables semantics buildSource w
  have e := exit_unique P.realize.run hrun
  exact ⟨e.1, out, e.2, hout⟩

end run

end
end NearCubicWires.SourcePhase
end
