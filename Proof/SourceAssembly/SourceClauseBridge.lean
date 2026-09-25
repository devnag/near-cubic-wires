import Proof.SourceAssembly.SourcePhaseLoop

/-! # SP's per-clause exits, reduced to the source's final bank `values.A N`, `values.H N`

**Consumer.** SP's `SourceClauseExit` (`source-phase-20260923/SourcePhaseFrame.lean:138`) and
`SourceClauseAppend` (`Proof/SourceAssembly/SourcePhaseLoop.lean`), owed by the per-clause cycle (map rows E1–E6). Both
speak about the site's exit `globalAfter`/`globalHnext`. `SourceTrace` fixes that exit only through
`_hfinalA`/`_hfinalH`:
- `globalAfter = install whole queried (pad counterCaps (cfg 3 (state N [])).tapes)`;
- `globalHnext = dockH whole globalH (cfg 3 (state N [])).heads`;
- `state N = ⟨body.start, values.H N, padded N⟩`.

**What this module proves.**
- `final_tape`: every body tape BELOW `F = offset+1155` exits as `values.A N` on the same index (the reserve
  and the counter caps are `0` there).
- `final_head`: every source tape exits with head `values.H N`.
- `clause_exit` and `clause_append`: SP's two structures follow from facts about `values.A N` and
  `values.H N` alone. Those are properties of the source's own bank chain (first cycle, family, refill), which
  the construction controls.

**Paper.** None (machine layer). The consumer is SP's typed per-clause interface. **Budget**: none (no machine).
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.ClauseBridge
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section bridge
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
  {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
  {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
  {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))}
  {n : Nat} {x : BitInput n}
  {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
  {bits : List Bool}
  {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
  {mode : Bool} {ph : Phase} {ci : Fin (NC sources k clock x oracle)}
  {globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat}
  {globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool}
  {b siteFuel : Nat}
  {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
  {values : RCFive.Source.SourceValues mask selector packets rows compiler sources p k den r scratch
      clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code}

theorem whole_injective
    (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) :
    Function.Injective code.whole := by
  intro i j h
  have e := congrArg Fin.val h
  rw [code._hwhole, code._hwhole] at e
  exact Fin.ext e

/-- The source universe contains every tape below `F = offset+1155` (the family slots start at `F`). -/
theorem F_lt (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) :
    PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 < code.sourceTapes := by
  have h := (code.slots ⟨0, by unfold r_tapes; omega⟩).isLt
  rw [code._hs] at h
  simpa using h

/-- **The site's exit below `F` is the source's final bank.** -/
theorem final_tape
    (tr : RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r scratch clock n x
      oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code values)
    (t : Fin code.sourceTapes) (ht : t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) :
    globalAfter (code.whole t.castSucc) = values.A values.entries.length t := by
  have h := congrFun tr._hfinalA (code.whole t.castSucc)
  rw [install_slot code.whole (whole_injective code)] at h
  rw [← h]
  have hU : (Fin.castSucc t).val ≠ code.sourceTapes := by simp; omega
  have hr : ¬ (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ t.val) := by omega
  simp only [RepeatMachine.cfg, controlConfig, TapeEmbedding.config, if_neg hU]
  rw [show Fin.castSucc t = Fin.castAdd 1 t from rfl, Fin.addCases_left]
  simp [ZeroPadding.pad, hr]

/-- **Every source tape exits at the source's final head.** -/
theorem final_head
    (tr : RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r scratch clock n x
      oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code values)
    (t : Fin code.sourceTapes) :
    globalHnext (code.whole t.castSucc) = values.H values.entries.length t := by
  have h := congrFun tr._hfinalH (code.whole t.castSucc)
  rw [dockH_slot code.whole (whole_injective code)] at h
  rw [← h]
  simp only [RepeatMachine.cfg, controlConfig, TapeEmbedding.config]
  rw [show Fin.castSucc t = Fin.castAdd 1 t from rfl, Fin.addCases_left]

/-- A body tape below `F` is `whole` of a source tape. -/
theorem below_F (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (ht : t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) :
    ∃ s : Fin code.sourceTapes, code.whole s.castSucc = t ∧ s.val = t.val :=
  ⟨⟨t.val, lt_trans ht (F_lt code)⟩, Fin.ext (by rw [code._hwhole]; rfl), rfl⟩

theorem region_lt {L v : Nat} (h : Region L v) : v < L + 1155 := by
  unfold Region at h; omega

theorem cache_lt (i : Fin 19) :
    (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val <
      PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 := by
  have h := cache_range sources p k r scratch mode i
  omega

/-- **SP's `SourceClauseExit`, from the source's final bank.** The premises are about `values.A N`,
`values.H N` (`N = entries.length`) on source tapes. -/
theorem clause_exit
    (tr : RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r scratch clock n x
      oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code values)
    (hA : ∀ s : Fin code.sourceTapes, Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) s.val →
      (∀ i, code.whole s.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) →
      code.whole s.castSucc ≠ Wd sources p k r scratch ph 81 →
      code.whole s.castSucc ≠ Wd sources p k r scratch ph 90 →
      values.A values.entries.length s = globalA (code.whole s.castSucc))
    (hH : ∀ s : Fin code.sourceTapes, Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) s.val →
      (∀ i, code.whole s.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) →
      values.H values.entries.length s = globalH (code.whole s.castSucc))
    (hcache : ∀ (i : Fin 19) (s : Fin code.sourceTapes),
      code.whole s.castSucc = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i →
      values.H values.entries.length s = 0 ∧ values.A values.entries.length s = CD sources k clock x oracle ci.val i) :
    SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site
      mode ph ci globalH globalHnext globalA globalAfter b siteFuel code values where
  _hkeep := by
    intro t hR hc h81 h90
    obtain ⟨s, hs, hsv⟩ := below_F code t (region_lt hR)
    subst hs
    rw [final_tape tr s (by rw [hsv]; exact region_lt hR)]
    exact hA s (by rw [hsv]; exact hR) hc h81 h90
  _hkeepH := by
    intro t hR hc
    obtain ⟨s, hs, hsv⟩ := below_F code t (region_lt hR)
    subst hs
    rw [final_head tr s]
    exact hH s (by rw [hsv]; exact hR) hc
  _hcacheH := by
    intro i
    obtain ⟨s, hs, _⟩ := below_F code _ (cache_lt i)
    rw [← hs, final_head tr s]
    exact (hcache i s hs).1
  _hrestored := by
    intro i
    obtain ⟨s, hs, hsv⟩ := below_F code _ (cache_lt i)
    rw [← hs, final_tape tr s (by rw [hsv]; exact cache_lt i)]
    exact (hcache i s hs).2

theorem wd_lt (j : Fin 278) :
    (Wd sources p k r scratch ph j).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 :=
  region_lt (wordSlots_region _ _ _ _ ph j)

/-- **SP's `SourceClauseAppend`, from the source's final bank** at the two append ports. -/
theorem clause_append
    (tr : RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r scratch clock n x
      oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code values)
    (happ : globalA (Wd sources p k r scratch ph 81) = Stream.words b values.phasePrefix →
      globalA (Wd sources p k r scratch ph 90) = CompareMachine.word values.phasePrefix.length →
      ∀ s81 s90 : Fin code.sourceTapes,
        code.whole s81.castSucc = Wd sources p k r scratch ph 81 →
        code.whole s90.castSucc = Wd sources p k r scratch ph 90 →
        values.A values.entries.length s81 = Stream.words b (values.phasePrefix ++ values.entries) ∧
        values.A values.entries.length s90 =
          CompareMachine.word (values.phasePrefix ++ values.entries).length)
    (hentries : ∀ j (hj : j < values.entries.length),
      values.entries[j] = (⟨values.coefficient j, values.total j, values.denominator j⟩ : Stream.Entry)) :
    SourceClauseAppend mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site
      mode ph ci globalH globalHnext globalA globalAfter b siteFuel code values where
  _happend := by
    intro h81 h90
    obtain ⟨s81, e81, v81⟩ := below_F code _ (wd_lt 81)
    obtain ⟨s90, e90, v90⟩ := below_F code _ (wd_lt 90)
    obtain ⟨a81, a90⟩ := happ h81 h90 s81 s90 e81 e90
    refine ⟨?_, ?_⟩
    · rw [← e81, final_tape tr s81 (by rw [v81]; exact wd_lt 81)]; exact a81
    · rw [← e90, final_tape tr s90 (by rw [v90]; exact wd_lt 90)]; exact a90
  _hentries := hentries

end bridge

end
end NearCubicWires.SourceConstruction.ClauseBridge
end
