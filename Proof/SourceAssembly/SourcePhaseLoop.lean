import Proof.SourceAssembly.SourcePhaseFrame

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

/-- **Per-clause append facts, in `SourceTrace`'s form.** OWED by the per-clause cycle. -/
structure SourceClauseAppend (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    (n : Nat) (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (bits : List Bool)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (mode : Bool) (ph : Phase)
    (ci : Fin (NC sources k clock x oracle))
    (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (b siteFuel : Nat)
    (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (values : RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch
      clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code) : Prop where
  /-- From the resident prefix, the clause appends its own entries and advances the count. -/
  _happend : globalA (Wd sources p k r scratch ph 81) = Stream.words b values.phasePrefix →
    globalA (Wd sources p k r scratch ph 90) = CompareMachine.word values.phasePrefix.length →
    globalAfter (Wd sources p k r scratch ph 81) = Stream.words b (values.phasePrefix ++ values.entries) ∧
    globalAfter (Wd sources p k r scratch ph 90) =
      CompareMachine.word (values.phasePrefix ++ values.entries).length
  /-- The appended entries are the clause's call records (row D3). -/
  _hentries : ∀ j (hj : j < values.entries.length),
    values.entries[j] = (⟨values.coefficient j, values.total j, values.denominator j⟩ : Stream.Entry)

/-! ## 1. Clause-ordered concatenation -/

/-- The clause-ordered concatenation of the first `j` clauses' entries. -/
def prefixEntries {m : Nat} (E : Fin m → List Stream.Entry) (j : Nat) : List Stream.Entry :=
  ((List.ofFn E).take j).flatten

theorem prefixEntries_zero {m : Nat} (E : Fin m → List Stream.Entry) : prefixEntries E 0 = [] := by
  simp [prefixEntries]

theorem prefixEntries_succ {m : Nat} (E : Fin m → List Stream.Entry) (j : Nat) (hj : j < m) :
    prefixEntries E (j+1) = prefixEntries E j ++ E ⟨j, hj⟩ := by
  simp only [prefixEntries, List.take_add_one, List.flatten_append, List.getElem?_ofFn]
  simp [hj]

theorem prefixEntries_all {m : Nat} (E : Fin m → List Stream.Entry) :
    prefixEntries E m = (List.ofFn E).flatten := by
  simp only [prefixEntries]
  rw [List.take_of_length_le (by simp)]

/-! ## 2. The phase fields -/

section phase
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {b siteFuel : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}

/-- The two append ports are not cache tapes. -/
theorem app_not_cache (j : Fin 278) (hj : j.val = 81 ∨ j.val = 90) :
    ∀ i, Wd sources p k r scratch ph j ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i :=
  not_cache sources p k r scratch mode _ (wd_ge_two ph j (by omega)) (wordSlots_region _ _ _ _ ph j)

/-- **E3** (`hcount`, `hstream`): after the loop the phase stream is the clause-ordered
concatenation of the clauses' entries, and the count is its length. -/
theorem fields_E3
    (H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : ∀ ci : Fin (NC sources k clock x oracle),
      RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch clock n x
        oracle bits site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code)
    (appends : ∀ ci : Fin (NC sources k clock x oracle),
      SourceClauseAppend mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
        site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci))
    (s_next : ∀ (j : Nat), j < NC sources k clock x oracle →
      A (j+1) = install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode) (s_after j)
        (CD sources k clock x oracle (j+1)))
    (hprefix : ∀ ci : Fin (NC sources k clock x oracle),
      (values ci).phasePrefix = prefixEntries (fun c => (values c).entries) ci.val)
    (N : Nat) (hN : N = 2^(pcppAt sources k clock x oracle).clauseBits)
    (e_stream : A 0 (Wd sources p k r scratch ph 81) = [])
    (e_count : A 0 (Wd sources p k r scratch ph 90) = CompareMachine.word 0) :
    A N (Wd sources p k r scratch ph 90) =
      CompareMachine.word (List.ofFn (fun c => (values c).entries)).flatten.length ∧
    A N (Wd sources p k r scratch ph 81) = Stream.words b (List.ofFn (fun c => (values c).entries)).flatten := by
  have hNC : N = NC sources k clock x oracle := N_eq_NC hN
  have c81 := app_not_cache (sources := sources) (p := p) (k := k) (r := r) (scratch := scratch) (ph := ph)
    (mode := mode) 81 (Or.inl rfl)
  have c90 := app_not_cache (sources := sources) (p := p) (k := k) (r := r) (scratch := scratch) (ph := ph)
    (mode := mode) 90 (Or.inr rfl)
  have ind : ∀ j, j ≤ NC sources k clock x oracle →
      A j (Wd sources p k r scratch ph 81) = Stream.words b (prefixEntries (fun c => (values c).entries) j) ∧
      A j (Wd sources p k r scratch ph 90) =
        CompareMachine.word (prefixEntries (fun c => (values c).entries) j).length := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [prefixEntries_zero, e_stream, e_count]
      exact ⟨rfl, rfl⟩
    | succ j ih =>
      intro hj
      have hjl : j < NC sources k clock x oracle := by omega
      obtain ⟨h81, h90⟩ := ih (by omega)
      have pre := hprefix ⟨j, hjl⟩
      have step := (appends ⟨j, hjl⟩)._happend (by rw [pre]; exact h81) (by rw [pre]; exact h90)
      rw [pre] at step
      rw [prefixEntries_succ _ j hjl, s_next j hjl,
        install_other _ (s_after j) _ _ (fun i he => c81 i he.symm),
        install_other _ (s_after j) _ _ (fun i he => c90 i he.symm)]
      exact step
  obtain ⟨h81, h90⟩ := ind N (Nat.le_of_eq hNC)
  rw [hNC, prefixEntries_all] at h81 h90
  rw [hNC]
  exact ⟨h90, h81⟩

/-- **E5** (`s_head s_terminal_head s_count s_cached`) from the loop start and the per-clause
exits. -/
theorem fields_E5
    (H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : ∀ ci : Fin (NC sources k clock x oracle),
      RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch clock n x
        oracle bits site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code)
    (exits : ∀ ci : Fin (NC sources k clock x oracle),
      SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
        site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci))
    (s_next : ∀ (j : Nat), j < NC sources k clock x oracle →
      A (j+1) = install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode) (s_after j)
        (CD sources k clock x oracle (j+1)))
    (e_cacheH : ∀ i, H 0 (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0)
    (e_termH : H 0 (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) = 0)
    (e_count : A 0 (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) =
      List.replicate (NC sources k clock x oracle) true)
    (e_cached : ∀ i, A 0 (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) =
      CD sources k clock x oracle 0 i) :
    (∀ (j : Nat), j ≤ NC sources k clock x oracle → ∀ (i : Fin 19),
      H j (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0) ∧
    (∀ (j : Nat), j < NC sources k clock x oracle →
      H j (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) = 0) ∧
    (∀ (j : Nat), j < NC sources k clock x oracle →
      A j (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) =
        List.replicate (NC sources k clock x oracle) true) ∧
    (∀ (j : Nat), j < NC sources k clock x oracle → ∀ (i : Fin 19),
      A j (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = CD sources k clock x oracle j i) := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have tR : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r)
      (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch).val := by
    right; left; rfl
  have tC := PCJ30aa6f1b7c2a4221_.Selected.cache_ne_terminal sources p k r scratch mode
  have tW : ∀ j : Fin 278, (j.val = 81 ∨ j.val = 90) →
      PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch ≠ Wd sources p k r scratch ph j := by
    intro j hj he
    have hv := congrArg Fin.val he
    rcases hj with hj | hj <;> cases ph <;>
    simp [Wd, PCJ30aa6f1b7c2a4221_.Selected.terminal, CloseoutFinalC10RetainedPhaseFold.wordSlots,
      CloseoutFinalC10RetainedPhaseFold.phaseBank, C10TailUniformSlots.phaseIndex, hj] at hv <;> omega
  refine ⟨phase_cacheH H A s_after values exits e_cacheH, ?_, ?_, ?_⟩
  · intro j hj
    rw [phase_keepH H A s_after values exits j (Nat.le_of_lt hj) _ tR (fun i he => tC i he.symm)]
    exact e_termH
  · intro j hj
    rw [phase_keep H A s_after values exits s_next j (Nat.le_of_lt hj) _ tR (fun i he => tC i he.symm)
      (tW 81 (Or.inl rfl)) (tW 90 (Or.inr rfl))]
    exact e_count
  · intro j hj i
    cases j with
    | zero => exact e_cached i
    | succ j =>
      rw [s_next j (by omega)]
      exact install_slot _ (PCJ30aa6f1b7c2a4221_.Selected.cache_injective sources p k r scratch mode) _ _ i

/-- **E6** (`s_restored`), from the per-clause exits. -/
theorem field_E6
    (H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : ∀ ci : Fin (NC sources k clock x oracle),
      RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch clock n x
        oracle bits site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code)
    (exits : ∀ ci : Fin (NC sources k clock x oracle),
      SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
        site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci)) :
    ∀ (j : Nat), j < NC sources k clock x oracle → ∀ (i : Fin 19),
      s_after j (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) =
        CD sources k clock x oracle j i :=
  fun j hj i => (exits ⟨j, hj⟩)._hrestored i

end phase

end
end NearCubicWires.SourcePhase
end
