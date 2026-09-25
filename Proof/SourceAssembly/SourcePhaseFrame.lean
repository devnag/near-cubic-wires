import Proof.SourceAssembly.SourceParent

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

/-! ## 1. The phase region, on plain numbers -/

/-- The phase region below the site's private universe `offset+1155`. -/
def Region (L v : Nat) : Prop := v < 278 ∨ v = L+53 ∨ (L+124 ≤ v ∧ v < L+1155)

theorem tailSlots_region (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) (i : Fin 475) :
    Region L (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh i).val := by
  have hi := i.isLt
  unfold Region CloseoutFinalC10RetainedPhaseFold.tailSlots
  dsimp only
  split_ifs <;> omega

theorem phaseBank_region (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) (ph : Phase) (i : Fin 278) :
    Region L (CloseoutFinalC10RetainedPhaseFold.phaseBank L B hL hFresh ph i).val := by
  have hi := i.isLt
  have hp := (C10TailUniformSlots.phaseIndex ph).isLt
  unfold Region CloseoutFinalC10RetainedPhaseFold.phaseBank
  dsimp only
  split_ifs <;> first | omega | (simp only; omega)

theorem wordSlots_region (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) (ph : Phase) (i : Fin 278) :
    Region L (CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i).val := by
  unfold CloseoutFinalC10RetainedPhaseFold.wordSlots
  split_ifs
  · exact tailSlots_region L B hL hFresh _
  · exact tailSlots_region L B hL hFresh _
  · exact phaseBank_region L B hL hFresh ph i

theorem foldSlots_region (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) (ph : Phase) (i : Fin 219) :
    Region L (CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph i).val := by
  unfold CloseoutFinalC10RetainedPhaseFold.foldSlots
  split_ifs
  · exact tailSlots_region L B hL hFresh _
  · exact tailSlots_region L B hL hFresh _
  · exact phaseBank_region L B hL hFresh ph _

/-! ## 2. The region against the body layout: the query cache sits at `{0,1} ∪ [P, offset)` -/

section layout
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)

theorem cache_range (mode : Bool) (i : Fin 19) :
    (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val < 2 ∨
    (302 ≤ (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val ∧
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val <
        PCJda54a286946142d3_BranchPhases.offset sources p k r) := by
  have hp : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
    unfold WorkspaceSelectedEntry.size
    omega
  have hc := (WorkspaceSelectedEntryReady.cache sources p k mode i).isLt
  change (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) < 2 ∨
    (302 ≤ (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) ∧
      (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) <
        PCJda54a286946142d3_BranchPhases.offset sources p k r)
  dsimp only [PCJda54a286946142d3_BranchPhases.offset]
  split_ifs <;> omega

/-- A region tape other than `0, 1` is never a cache tape. -/
theorem not_cache (mode : Bool) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h2 : 2 ≤ t.val) (hR : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val) :
    ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i := by
  intro i he
  have hc := cache_range sources p k r scratch mode i
  rw [← he] at hc
  unfold Region at hR
  omega

end layout

/-! ## 3. The per-clause exit fact the phase loop consumes (owed by the per-clause cycle) -/

/-- **Per-clause exit facts, in `SourceTrace`'s form** (same parameters; `code`, `values` are the
clause's fixed code and per-call values). `SourceTrace` fixes the clause exit `globalAfter` /
`globalHnext` through the per-call bank `values.A` (`_hfinalA/_hfinalH`) but states no frame for
it; these are the facts about that exit the phase level reads. OWED by the per-clause cycle. -/
structure SourceClauseExit (mask : MaskProducer) (selector : CyclicChoice.Laws)
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
  /-- The site writes nothing in the phase region off the cache and its two append ports. -/
  _hkeep : ∀ t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch),
    Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val →
    (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) →
    t ≠ Wd sources p k r scratch ph 81 → t ≠ Wd sources p k r scratch ph 90 →
    globalAfter t = globalA t
  /-- It moves no head in the phase region off the cache. -/
  _hkeepH : ∀ t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch),
    Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val →
    (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) →
    globalHnext t = globalH t
  /-- It returns the cache heads to 0 (`MaskedPhase._s_head` at `ci+1`). -/
  _hcacheH : ∀ i, globalHnext (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0
  /-- It restores the cache to the empty-query state (`MaskedPhase._s_restored` at `ci`, row E6). -/
  _hrestored : ∀ i, globalAfter (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) =
    CD sources k clock x oracle ci.val i

/-! ## 4. The generic loop frame (over `s_next`) -/

/-- Contents kept by every clause stay at their loop-start value. -/
theorem loop_keep {B : Nat} (NC : Nat) (cache : Fin 19 → Fin B) (CD : Nat → Fin 19 → List Bool)
    (A s_after : Nat → Fin B → List Bool) (keep : Fin B → Prop)
    (hkeep : ∀ t, keep t → ∀ i, t ≠ cache i)
    (s_next : ∀ j, j < NC → A (j+1) = install cache (s_after j) (CD (j+1)))
    (hstep : ∀ j, j < NC → ∀ t, keep t → s_after j t = A j t) :
    ∀ j, j ≤ NC → ∀ t, keep t → A j t = A 0 t := by
  intro j
  induction j with
  | zero => intro _ t _; rfl
  | succ j ih =>
    intro hj t ht
    rw [s_next j (by omega), install_other cache (s_after j) (CD (j+1)) t
      (fun i he => hkeep t ht i he.symm), hstep j (by omega) t ht]
    exact ih (by omega) t ht

/-- Heads kept by every clause stay at their loop-start value. -/
theorem loop_keepH {B : Nat} (NC : Nat) (H : Nat → Fin B → Nat) (keep : Fin B → Prop)
    (hstep : ∀ j, j < NC → ∀ t, keep t → H (j+1) t = H j t) :
    ∀ j, j ≤ NC → ∀ t, keep t → H j t = H 0 t := by
  intro j
  induction j with
  | zero => intro _ t _; rfl
  | succ j ih =>
    intro hj t ht
    rw [hstep j (by omega) t ht]
    exact ih (by omega) t ht

/-! ## 5. The phase loop, from the per-clause exits -/

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

/-- The phase region off the cache and the phase's append ports is unchanged across the loop. -/
theorem phase_keep
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
        (CD sources k clock x oracle (j+1))) :
    ∀ j, j ≤ NC sources k clock x oracle → ∀ t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch),
      Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val →
      (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) →
      t ≠ Wd sources p k r scratch ph 81 → t ≠ Wd sources p k r scratch ph 90 →
      A j t = A 0 t := by
  intro j hj t hR hc h81 h90
  exact loop_keep (NC sources k clock x oracle)
    (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode) (CD sources k clock x oracle)
    A s_after
    (fun t => Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val ∧
      (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) ∧
      t ≠ Wd sources p k r scratch ph 81 ∧ t ≠ Wd sources p k r scratch ph 90)
    (fun t ht => ht.2.1) s_next
    (fun j hj t ht => (exits ⟨j, hj⟩)._hkeep t ht.1 ht.2.1 ht.2.2.1 ht.2.2.2)
    j hj t ⟨hR, hc, h81, h90⟩

/-- The heads in the phase region off the cache are unchanged across the loop. -/
theorem phase_keepH
    (H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : ∀ ci : Fin (NC sources k clock x oracle),
      RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch clock n x
        oracle bits site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code)
    (exits : ∀ ci : Fin (NC sources k clock x oracle),
      SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
        site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci)) :
    ∀ j, j ≤ NC sources k clock x oracle → ∀ t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch),
      Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val →
      (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) →
      H j t = H 0 t := by
  intro j hj t hR hc
  exact loop_keepH (NC sources k clock x oracle) H
    (fun t => Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val ∧
      (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i))
    (fun j hj t ht => (exits ⟨j, hj⟩)._hkeepH t ht.1 ht.2)
    j hj t ⟨hR, hc⟩

/-- `MaskedPhase._s_head` for `j ≥ 1`: the cache heads after every clause are 0. -/
theorem phase_cacheH
    (H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : ∀ ci : Fin (NC sources k clock x oracle),
      RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch clock n x
        oracle bits site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code)
    (exits : ∀ ci : Fin (NC sources k clock x oracle),
      SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
        site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci))
    (h0 : ∀ i, H 0 (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0) :
    ∀ (j : Nat), j ≤ NC sources k clock x oracle → ∀ (i : Fin 19),
      H j (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0 := by
  intro j hj i
  cases j with
  | zero => exact h0 i
  | succ j => exact (exits ⟨j, by omega⟩)._hcacheH i

/-! ## 6. The consumer fields at the loop exit `A N`/`H N` -/

/-- The consumer's `N` (field `hN`) is the clause count. -/
theorem N_eq_NC {N : Nat} (hN : N = 2^(pcppAt sources k clock x oracle).clauseBits) :
    N = NC sources k clock x oracle := hN

/-- Word slots at index `≥ 2` sit at tapes `≥ 2`. -/
theorem wd_ge_two (ph' : Phase) (i : Fin 278) (h2 : 2 ≤ i.val) :
    2 ≤ (Wd sources p k r scratch ph' i).val := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hi := i.isLt
  have hp := (C10TailUniformSlots.phaseIndex ph').isLt
  simp only [Wd, CloseoutFinalC10RetainedPhaseFold.wordSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    CloseoutFinalC10RetainedPhaseFold.phaseBank]
  split_ifs <;> first | omega | (simp only; omega)

/-- Fold slots sit at tapes `≥ 2` from index 2 on. -/
theorem fd_ge_two (ph' : Phase) (i : Fin 219) (h2 : 2 ≤ i.val) :
    2 ≤ (Fd sources p k r scratch ph' i).val := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hi := i.isLt
  have hp := (C10TailUniformSlots.phaseIndex ph').isLt
  simp only [Fd, CloseoutFinalC10RetainedPhaseFold.foldSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    CloseoutFinalC10RetainedPhaseFold.phaseBank]
  split_ifs <;> first | omega | (simp only; omega)

/-- The two fold slots the consumer blanks are not the phase's append ports. -/
theorem fd_ne_app (ph' : Phase) (i : Fin 219) (hi : i.val = 215 ∨ i.val = 218) (j : Fin 278)
    (hj : j.val = 81 ∨ j.val = 90) :
    Fd sources p k r scratch ph' i ≠ Wd sources p k r scratch ph' j := by
  intro he
  have hv := congrArg Fin.val he
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
  cases ph' <;>
  simp [Fd, Wd, CloseoutFinalC10RetainedPhaseFold.foldSlots, CloseoutFinalC10RetainedPhaseFold.wordSlots,
    CloseoutFinalC10RetainedPhaseFold.tailSlots, CloseoutFinalC10RetainedPhaseFold.phaseBank,
    C10TailVerdict.scratchT, C10TailUniformSlots.phaseIndex, hi, hj] at hv

/-- **E4** (`hblank hfresh hrecord hlog`): the phase bank's blank cells at the loop exit, from
the loop start. -/
theorem fields_E4
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
    (N : Nat) (hN : N = 2^(pcppAt sources k clock x oracle).clauseBits)
    (e_blank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 →
      A 0 (Wd sources p k r scratch ph i) = [])
    (e_fresh : ∀ i : Fin 278, 219 ≤ i.val → A 0 (Wd sources p k r scratch ph i) = [])
    (e_record : A 0 (Fd sources p k r scratch ph 215) = [])
    (e_log : A 0 (Fd sources p k r scratch ph 218) = []) :
    (∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 →
      A N (Wd sources p k r scratch ph i) = []) ∧
    (∀ i : Fin 278, 219 ≤ i.val → A N (Wd sources p k r scratch ph i) = []) ∧
    A N (Fd sources p k r scratch ph 215) = [] ∧ A N (Fd sources p k r scratch ph 218) = [] := by
  have hNC : N ≤ NC sources k clock x oracle := Nat.le_of_eq (N_eq_NC hN)
  have hwi := (CloseoutFinalC10RetainedPhaseFold.maps_injective
    (PCJda54a286946142d3_BranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
    (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) ph).1
  have keepW : ∀ i : Fin 278, 2 ≤ i.val → i.val ≠ 81 → i.val ≠ 90 →
      A N (Wd sources p k r scratch ph i) = A 0 (Wd sources p k r scratch ph i) := by
    intro i h2 h81 h90
    exact phase_keep H A s_after values exits s_next N hNC _
      (wordSlots_region _ _ _ _ ph i)
      (not_cache sources p k r scratch mode _ (wd_ge_two ph i h2) (wordSlots_region _ _ _ _ ph i))
      (fun he => h81 (congrArg Fin.val (hwi he)))
      (fun he => h90 (congrArg Fin.val (hwi he)))
  have keepF : ∀ i : Fin 219, (i.val = 215 ∨ i.val = 218) →
      A N (Fd sources p k r scratch ph i) = A 0 (Fd sources p k r scratch ph i) := by
    intro i hi
    have h2 : 2 ≤ i.val := by omega
    exact phase_keep H A s_after values exits s_next N hNC _
      (foldSlots_region _ _ _ _ ph i)
      (not_cache sources p k r scratch mode _ (fd_ge_two ph i h2) (foldSlots_region _ _ _ _ ph i))
      (fd_ne_app ph i hi 81 (Or.inl rfl)) (fd_ne_app ph i hi 90 (Or.inr rfl))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i h2 h215 h81 h90
    rw [keepW i h2 h81 h90]
    exact e_blank i h2 h215 h81 h90
  · intro i h219
    rw [keepW i (by omega) (by omega) (by omega)]
    exact e_fresh i h219
  · rw [keepF 215 (Or.inl rfl)]
    exact e_record
  · rw [keepF 218 (Or.inr rfl)]
    exact e_log

/-- **E2** (`hwidthDriver`): the width driver on word slot 218 survives the loop. -/
theorem field_E2
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
    (N : Nat) (hN : N = 2^(pcppAt sources k clock x oracle).clauseBits) (w : Nat)
    (e_driver : A 0 (Wd sources p k r scratch ph 218) = List.replicate w true) :
    A N (Wd sources p k r scratch ph 218) = List.replicate w true := by
  have hNC : N ≤ NC sources k clock x oracle := Nat.le_of_eq (N_eq_NC hN)
  have hwi := (CloseoutFinalC10RetainedPhaseFold.maps_injective
    (PCJda54a286946142d3_BranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
    (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) ph).1
  rw [phase_keep H A s_after values exits s_next N hNC _
    (wordSlots_region _ _ _ _ ph 218)
    (not_cache sources p k r scratch mode _ (wd_ge_two ph 218 (by decide)) (wordSlots_region _ _ _ _ ph 218))
    (fun he => absurd (congrArg Fin.val (hwi he)) (by decide))
    (fun he => absurd (congrArg Fin.val (hwi he)) (by decide))]
  exact e_driver

/-- **E1** (`hHw hHf`): every word/fold slot head is 0 at the loop exit, from the loop start and
the cache heads at the loop start (`_s_head` at `j = 0`). -/
theorem fields_E1
    (H : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : ∀ ci : Fin (NC sources k clock x oracle),
      RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch clock n x
        oracle bits site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code)
    (exits : ∀ ci : Fin (NC sources k clock x oracle),
      SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
        site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel code (values ci))
    (N : Nat) (hN : N = 2^(pcppAt sources k clock x oracle).clauseBits)
    (e_cacheH : ∀ i, H 0 (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0)
    (e_Hw : ∀ i, H 0 (Wd sources p k r scratch ph i) = 0)
    (e_Hf : ∀ i, H 0 (Fd sources p k r scratch ph i) = 0) :
    (∀ i, H N (Wd sources p k r scratch ph i) = 0) ∧ (∀ i, H N (Fd sources p k r scratch ph i) = 0) := by
  have hNC : N ≤ NC sources k clock x oracle := Nat.le_of_eq (N_eq_NC hN)
  have cacheN := phase_cacheH H A s_after values exits e_cacheH N hNC
  have gen : ∀ t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch),
      Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val → H 0 t = 0 → H N t = 0 := by
    intro t hR h0
    by_cases hc : ∃ i, t = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i
    · obtain ⟨i, rfl⟩ := hc
      exact cacheN i
    · have hc' : ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i :=
        fun i he => hc ⟨i, he⟩
      rw [phase_keepH H A s_after values exits N hNC t hR hc']
      exact h0
  exact ⟨fun i => gen _ (wordSlots_region _ _ _ _ ph i) (e_Hw i),
    fun i => gen _ (foldSlots_region _ _ _ _ ph i) (e_Hf i)⟩

end phase

end
end NearCubicWires.SourcePhase
end
