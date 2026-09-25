import Proof.CaseAnalysis.FinalUnaryExpDock

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Res284
open NearCubicWires NearCubicWires.ExtDecompositionBatch NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutFinalC10UnaryExpDock NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines
noncomputable section

/-- The exponentiator's work word: `frame (binary (d+3) (2^d))`. -/
abbrev expWork (d : ℕ) : List Bool := RepairOrdinary.frame (RepairOrdinary.SignedSortKey.binary (d+3) (2^d))

theorem expWork_length (d : ℕ) : (expWork d).length = 2*d + 7 := by
  simp [expWork, RepairOrdinary.frame_length]
  omega

section power
open NearCubicWires.RepairSource.CloseoutCapacity.Power

/-- `Power.power_run` with the work tape 6. -/
theorem power_run6 (d : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget d) (input d) out ∧
      out 15 = List.replicate (2^d) true ∧ out 13 = UnaryTemplate.tape (2^d) ∧ out 6 = expWork d := by
  obtain ⟨a,ha,_,_,h6,hat,_,_,hs⟩:=MatrixScorePower.power_run d
  obtain ⟨r,hr,rt,rh,rs,_⟩:=Rewind.reset_run MatrixScorePower.machine _ _ a ha
  have hp : ClockJoin.ReadyRun (Rewind.machine MatrixScorePower.machine) (2*a.steps+2)
      (Fin.addCases (motive:=fun _ : Fin 15=>List Bool) (MatrixScorePower.input d) (fun _ : Fin 1=>[]))
      r.final.tapes := ⟨r,hr,rfl,rh,rs.le⟩
  have hbig:=ClockJoin.enlarge _ _ _ _ _ hp (by omega : 2*a.steps+2 ≤ 2*MatrixScorePower.budget d+2)
  have hsf:=hbig.focus sourceSlots source_injective (input d) (by
    intro i;fin_cases i <;> rfl)
  let middle:=install sourceSlots (input d) r.final.tapes
  change ClockJoin.ReadyRun source (2*MatrixScorePower.budget d+2) (input d) middle at hsf
  have hm : middle 13=UnaryTemplate.tape (2^d) := by
    change install sourceSlots _ _ (sourceSlots 13)=_
    rw [install_slot _ source_injective]
    exact (rt 13).trans hat
  have hm6 : middle 6 = expWork d := by
    change install sourceSlots _ _ (sourceSlots 6)=_
    rw [install_slot _ source_injective]
    exact (rt 6).trans h6
  have hcf:=(UWalkUnary.ready false false (2^d+2) (2^d)).focus copySlots (by decide) middle (by
    intro i;fin_cases i
    · change middle 13=UWalkUnary.source (2^d+2) (2^d)
      rw [template_source]
      exact hm
    all_goals
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj;have h:=congrArg Fin.val hj;have:=j.isLt;dsimp [sourceSlots,RepairSource.CloseoutCapacity.Power.copySlots] at h;omega)]
      rfl)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hsf hcf,?_,?_,?_⟩
  · change install copySlots _ _ (copySlots 1)=_
    rw [install_slot _ (by decide)]
    simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead]
  · change install copySlots _ _ (copySlots 0)=_
    rw [install_slot _ (by decide)]
    exact template_source (2^d)
  · change install copySlots _ _ 6 = _
    rw [install_other _ _ _ _ (by decide)]
    exact hm6

end power

/-- `exp_dock` with the work tape 6. -/
theorem exp_dock6 {m : ℕ} (d : ℕ) (slots : Fin 17 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate d true)
    (hblank : ∀ j : Fin 17, j ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots RepairSource.CloseoutCapacity.Power.machine)
        (RepairSource.CloseoutCapacity.Power.budget d) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 15) = List.replicate (2 ^ d) true ∧
      A' (slots 13) = UnaryTemplate.tape (2 ^ d) ∧
      A' (slots 6) = expWork d ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨out, ⟨rc, hrun, ht, hh, hs⟩, h15, h13, h6⟩ := power_run6 d
  have hstep : Step RepairSource.CloseoutCapacity.Power.machine
      (RepairSource.CloseoutCapacity.Power.budget d) (fun _ => 0)
      (RepairSource.CloseoutCapacity.Power.input d) (fun _ => 0) out :=
    ⟨rc, hrun, funext hh, ht, hs⟩
  have hA : ∀ j : Fin 17, A (slots j) = RepairSource.CloseoutCapacity.Power.input d j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simpa [RepairSource.CloseoutCapacity.Power.input] using h0
    · rw [powerInput_other d j hj]
      exact hblank j hj
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_, ?_⟩
  · exact (install_slot slots hinj A out 15).trans h15
  · exact (install_slot slots hinj A out 13).trans h13
  · exact (install_slot slots hinj A out 6).trans h6
  · intro i hi
    exact install_other slots A out i hi

theorem powIdx_six : powIdx 6 = (6 : Fin 20) := by decide
theorem cntIdx_ne_six : ∀ j : Fin 4, cntIdx j ≠ (6 : Fin 20) := by decide

/-- `expWord_dock` with the work tape 6. -/
theorem expWord_dock6 {m : ℕ} (d : ℕ) (slots : Fin 20 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate d true)
    (hblank : ∀ j : Fin 20, j ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (expWordMachine slots)
        (RepairSource.CloseoutCapacity.Power.budget d + 1 +
          RepairSource.ProjectionNormalization.Counter.budget (2 ^ d)) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 15) = List.replicate (2 ^ d) true ∧
      A' (slots 13) = UnaryTemplate.tape (2 ^ d) ∧
      A' (slots 18) = CompareMachine.word (2 ^ d) ∧
      A' (slots 6) = expWork d ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨H₁, A₁, hstep₁, hzero₁, p15, p13, p6, prest⟩ :=
    exp_dock6 d (fun j => slots (powIdx j)) (hinj.comp powIdx_injective) H A hH
      (by simpa only [powIdx_zero] using h0)
      (fun j hj => hblank (powIdx j) (powIdx_ne_zero j hj))
  have q15 : A₁ (slots 15) = List.replicate (2 ^ d) true := by
    simpa only [powIdx_fifteen] using p15
  have q13 : A₁ (slots 13) = UnaryTemplate.tape (2 ^ d) := by
    simpa only [powIdx_thirteen] using p13
  have q6 : A₁ (slots 6) = expWork d := by
    simpa only [powIdx_six] using p6
  have q17 : A₁ (slots 17) = [] :=
    (prest (slots 17) (fun j => hinj.ne (powIdx_ne_seventeen j))).trans
      (hblank 17 (by decide))
  have q18 : A₁ (slots 18) = [] :=
    (prest (slots 18) (fun j => hinj.ne (powIdx_ne_eighteen j))).trans
      (hblank 18 (by decide))
  have q19 : A₁ (slots 19) = [] :=
    (prest (slots 19) (fun j => hinj.ne (powIdx_ne_nineteen j))).trans
      (hblank 19 (by decide))
  obtain ⟨H₂, A₂, hstep₂, hzero₂, r0, r2, rrest⟩ :=
    counter_dock (2 ^ d) (fun j => slots (cntIdx j)) (hinj.comp cntIdx_injective) H₁ A₁ hzero₁
      (by simpa only [cntIdx_zero] using q15)
      (by simpa only [cntIdx_one] using q17)
      (by simpa only [cntIdx_two] using q18)
      (by simpa only [cntIdx_three] using q19)
  refine ⟨H₂, A₂, hstep₁.seq hstep₂, hzero₂, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [cntIdx_zero] using r0
  · exact (rrest (slots 13) (fun j => hinj.ne (cntIdx_ne_thirteen j))).trans q13
  · simpa only [cntIdx_two] using r2
  · exact (rrest (slots 6) (fun j => hinj.ne (cntIdx_ne_six j))).trans q6
  · intro i hi
    exact (rrest i (fun j => hi (cntIdx j))).trans (prest i (fun j => hi (powIdx j)))

/-- `envelopeCounter_dock` with the work tape 6. -/
theorem envelopeCounter_dock6 {m : ℕ} (clauseDegree q : ℕ) (slots : Fin 20 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) =
      List.replicate (RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) true)
    (hblank : ∀ j : Fin 20, j ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (expWordMachine slots)
        (RepairSource.CloseoutCapacity.Power.budget
            (RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) + 1 +
          RepairSource.ProjectionNormalization.Counter.budget
            (2 ^ RepairSource.CloseoutLanguage.clauseWidth clauseDegree q)) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 15) =
        List.replicate (2 ^ RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) true ∧
      A' (slots 18) =
        CompareMachine.word (2 ^ RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) ∧
      A' (slots 6) = expWork (RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨H', A', hstep, hzero, g15, _, g18, g6, grest⟩ :=
    expWord_dock6 (RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) slots hinj H A hH
      h0 hblank
  exact ⟨H', A', hstep, hzero, g15, g18, g6, grest⟩

end
end NearCubicWires.SourceStart.Res284

