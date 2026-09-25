import Proof.Packets.SrcRes284Pro
import Proof.Assembly.CappedReady

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Res284
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairOrdinary.CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration CanonicalWitnessCodec
open WorkspaceSelectedAdmission (originalTapes capacity)
open WorkspaceSelectedProgram (finalBank)
open RecoveryRootRound
open WorkspaceSelectedEntryReady
open private NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.cache_injective from Proof.CaseAnalysis.FinalAdmittedEntry
noncomputable section

/-- **Determinism**: one machine from one entry reaches one exit bank, whatever the two fuels. -/
theorem tapes_det {t s : ℕ} {m : Machine t s} {f1 f2 : ℕ} {H J J' : Fin t → ℕ} {A B B' : Fin t → List Bool}
    (h : Step m f1 H A J B) (h' : Step m f2 H A J' B') : B = B' := by
  have h1 := h.enlarge (Nat.le_add_right f1 f2)
  have h2 := h'.enlarge (Nat.le_add_left f2 f1)
  obtain ⟨r, hr, _, ht, _⟩ := h1
  obtain ⟨r', hr', _, ht', _⟩ := h2
  have same : r = r' := Option.some.inj (hr.symm.trans hr')
  exact ht.symm.trans ((congrArg (fun e => e.final.tapes) same).trans ht')

/-- **The ready bank's tape `originalTapes + 2 + 284` is the exponentiator's work word.** -/
theorem readyBank_284 (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r extra : Nat)
    (hspace : WorkspaceSelectedEntry.size sources k r p.clauseDegree + 96 ≤ extra)
    (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) :
    PCJ687b3b71abe848ce_.readyBank sources p den hden k r extra hspace n x bits hp
        ⟨originalTapes sources p k + 2 + 284, by unfold WorkspaceSelectedEntry.size at hspace; omega⟩ =
      expWork (RepairSource.CloseoutLanguage.clauseWidth p.clauseDegree (C10PartsSchedule.widthAt sources k n)) := by
  -- the admitted bank (as in `ready_run`)
  let receipt := ControllerCappedSelected.selected_run sources p den hden k
    (PolynomialClock.ordinaryClock k) extra n x bits
  let A := receipt.choose
  let L := receipt.choose_spec.choose
  have hr := receipt.choose_spec.choose_spec.1
  have ho := PCJ138fdb4302e34c7e_CappedOriginals.originals_of_run
    sources gamma p den hden k (PolynomialClock.ordinaryClock k) extra n x bits A L hr hp
  have hc := receipt.choose_spec.choose_spec.2.2.1 hp
  
  let source := fixedProjection sources
  let a := CloseoutLanguage.selectedPCPP sources
  let CH := (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
  let Cpad := padding sources k (PolynomialClock.ordinaryClock k)
  let code := SelectedSource.code sources k (PolynomialClock.ordinaryClock k)
  obtain ⟨_oldH, oracle, _hdecode, _hsize, fields⟩ := hc
  let rq := ColdNative.request source a k CH Cpad code x (Nat.le_max_right _ _) oracle
  have cacheBytes : ∀ j, A (cache sources p k (BoundedFields.symmetric bits) j) = WorkspaceSelectedEntryCount.cacheData a rq j :=
    fun j => (fields j).1
  obtain ⟨w, hpre, _keep, h284⟩ := entry_run6 sources p k r extra (by omega) n x bits A L ho
  have ci := NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.cache_injective source a k p.clauseDegree p.degree
    (capacity sources p).E (BoundedFields.symmetric bits)
  obtain ⟨out, hin, _cacheKeep, _actualCount, _raw, _recordWidth, _keep2⟩ := WorkspaceSelectedEntryInit.run_init
    sources k r p.clauseDegree n (originalTapes sources p k) extra (old_size sources p k) hspace
    A L (List.ofFn x) bits w (cache sources p k (BoundedFields.symmetric bits)) ci a rq ho.1 ho.2.1 cacheBytes
  have modeTape : post sources p k r extra hspace A L n (List.ofFn x) bits w (modePort sources p k extra) =
      [BoundedFields.symmetric bits] :=
    (WorkspaceSelectedEntryFacts.old_bank_retained sources k r p.clauseDegree n _ extra (old_size sources p k)
      (by omega) A L (List.ofFn x) bits w ho.1 ho.2.1 _).trans ho.2.2
  have modeHead : heads sources p k r extra hspace (modePort sources p k extra) = 0 :=
    WorkspaceSelectedEntryInit.old_heads_zero sources k r p.clauseDegree _ extra (old_size sources p k) (by omega) _
  have readMode : readTapeBit (post sources p k r extra hspace A L n (List.ofFn x) bits w (modePort sources p k extra))
      (heads sources p k r extra hspace (modePort sources p k extra)) = BoundedFields.symmetric bits := by
    rw [modeTape, modeHead]; rfl
  have switched : Step (initializer sources p k r extra hspace)
      (WorkspaceSelectedEntryCount.budget a rq (C10PartsSchedule.entryWidthSchedule sources k r n)+2)
      (heads sources p k r extra hspace) (post sources p k r extra hspace A L n (List.ofFn x) bits w)
      (heads sources p k r extra hspace)
      (install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
        (post sources p k r extra hspace A L n (List.ofFn x) bits w) out) := by
    cases hm : BoundedFields.symmetric bits
    · rw [hm] at hin readMode
      exact CloseoutRowsOriginalSwitch.false_run _ _ _ hin readMode
    · rw [hm] at hin readMode
      exact CloseoutRowsOriginalSwitch.true_run _ _ _ hin readMode
  have last := switched.seq (bump_run sources p k r extra hspace _)
  have whole := hpre.seq last
  have whole' : Step (program sources p k r extra hspace).2
      (C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n + 1 +
        (WorkspaceSelectedEntryCount.budget a rq (C10PartsSchedule.entryWidthSchedule sources k r n) + 2 + 1 + 1))
      (fun _ => 0) (finalBank A L extra)
      (finalHeads sources p k r extra hspace)
      (install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
        (post sources p k r extra hspace A L n (List.ofFn x) bits w) out) := by
    unfold program
    exact whole
  have same := tapes_det whole' (PCJ687b3b71abe848ce_.ready_step sources p den hden k r extra hspace n x bits hp)
  rw [← same]
  -- evaluate at the prologue's local 284
  have hsz : 284 + 1 < WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
    unfold WorkspaceSelectedEntry.size; omega
  have eG : (⟨originalTapes sources p k + 2 + 284, by unfold WorkspaceSelectedEntry.size at hspace; omega⟩ :
      Fin (originalTapes sources p k + 1 + 1 + extra)) =
      proPort sources p k r extra hspace ⟨284, by omega⟩ := by
    apply Fin.ext
    simp [proPort, WorkspaceSelectedEntry.slots]
  rw [install_other _ _ _ _ ?_]
  · rw [eG]
    unfold post
    rw [install_slot (proPort sources p k r extra hspace) (WorkspaceSelectedEntry.slots_injective _ _)]
    unfold WorkspaceSelectedEntry.output
    rw [show (⟨284, by omega⟩ : Fin (WorkspaceSelectedEntry.size sources k r p.clauseDegree)) =
        Fin.castAdd 1 (⟨284, by omega⟩ :
          Fin (218 + (60 + (WorkspaceSelectedEntry.engineTapes sources k r p.clauseDegree + 23)))) from Fin.ext rfl,
      Fin.addCases_left]
    show C10SupplierCall.bankAt _ _ _ _ _ w 284 = _
    unfold C10SupplierCall.bankAt
    simp only [show (284:ℕ) ≠ 0 by decide, show (284:ℕ) ≠ 1 by decide, show (284:ℕ) ≠ 81 by decide,
      show (284:ℕ) ≠ 90 by decide, show (284:ℕ) ≠ 216 by decide, show (284:ℕ) ≠ 218 by decide, if_false,
      show (278:ℕ) ≤ 284 by decide, if_true]
    exact h284
  · intro i hi
    have hv := congrArg Fin.val hi
    unfold initPort WorkspaceSelectedEntryInit.ports at hv
    split_ifs at hv with h1 h2
    · have := (cache sources p k (BoundedFields.symmetric bits) ⟨i.val, h1⟩).isLt
      simp at hv
      omega
    · simp at hv
    · simp at hv
      unfold WorkspaceSelectedEntry.size at hv
      omega

end
end NearCubicWires.SourceStart.Res284

