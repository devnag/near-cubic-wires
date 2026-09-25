import Proof.Rows.RowsInitLive
import Proof.Rows.RowsInitLoopWords

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RowsInit.LoopAux
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta RowsInit.LoopWords
noncomputable section

/-! ## 1. `x ↦ x/2` (bespoke: skip a cell, copy a cell) -/

namespace Halve

/-- States: 0 skip a cell, 1 copy a cell, 2 halt. Tape 0 the input `1^x`, tape 1 the output. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q b =>
    if q.val = 0 then
      if b 0 then some ⟨1, fun _ => none, fun i => if i.val = 0 then .right else .stay⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else if q.val = 1 then
      if b 0 then some ⟨0, fun i => if i.val = 1 then some true else none, fun _ => .right⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else none

def cfg (x : ℕ) (q : Fin 3) (i o : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, o], ![List.replicate x true, List.replicate o true]⟩

theorem skip (x i o : ℕ) (hi : i < x) : step machine (cfg x 0 i o) = some (cfg x 1 (i + 1) o) := by
  have hr : readTapeBit (List.replicate x true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem copy (x i o : ℕ) (hi : i < x) : step machine (cfg x 1 i o) = some (cfg x 0 (i + 1) (o + 1)) := by
  have hr : readTapeBit (List.replicate x true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stopA (x o : ℕ) : step machine (cfg x 0 x o) = some (cfg x 2 x o) := by
  have hr : readTapeBit (List.replicate x true) x = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stopB (x o : ℕ) : step machine (cfg x 1 x o) = some (cfg x 2 x o) := by
  have hr : readTapeBit (List.replicate x true) x = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem pairs (x j i o : ℕ) (h : i + 2 * j ≤ x) :
    Timed machine (2 * j) (cfg x 0 i o) (cfg x 0 (i + 2 * j) (o + j)) := by
  induction j generalizing i o with
  | zero => exact Timed.refl _ _
  | succ j ih =>
    have e : 2 * (j + 1) = 1 + (1 + 2 * j) := by ring
    have h2 := ih (i + 1 + 1) (o + 1) (by omega)
    have e2 : i + 1 + 1 + 2 * j = i + 2 * (j + 1) := by ring
    have e3 : o + 1 + j = o + (j + 1) := by ring
    rw [e2, e3] at h2
    have h := (Timed.single (p := machine) (by rfl) (skip x i o (by omega))).trans
      ((Timed.single (p := machine) (by rfl) (copy x (i + 1) o (by omega))).trans h2)
    rw [← e] at h
    exact h

theorem timed (x : ℕ) : Timed machine (x + 1) (cfg x 0 0 0) (cfg x 2 x (x / 2)) := by
  have hp := pairs x (x / 2) 0 0 (by omega)
  rw [Nat.zero_add, Nat.zero_add] at hp
  rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
  · have e1 : 2 * (x / 2) = x := by omega
    rw [e1] at hp
    exact hp.trans (Timed.single (by rfl) (stopA x (x / 2)))
  · have e1 : 2 * (x / 2) + 1 = x := by omega
    have h1 := Timed.single (p := machine) (by rfl) (skip x (2 * (x / 2)) (x / 2) (by omega))
    rw [e1] at h1
    have h := (hp.trans h1).trans (Timed.single (by rfl) (stopB x (x / 2)))
    have e : 2 * (x / 2) + 1 + 1 = x + 1 := by omega
    rw [e] at h
    exact h

theorem run (x : ℕ) :
    Step machine (x + 1) (fun _ => 0) ![List.replicate x true, []] ![x, x / 2]
      ![List.replicate x true, List.replicate (x / 2) true] := by
  obtain ⟨r, hr, hf, _⟩ := (timed x).run (by rfl)
  have hc : cfg x 0 0 0 = (⟨machine.start, fun _ => 0, ![List.replicate x true, []]⟩ : Configuration 2 3) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hc] at hr
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

end Halve

/-- **`x ↦ x/2`** as PG's `UnaryMap` (masked reset, log entering empty). -/
def halveMap : UnaryMap (fun x => x / 2) where
  extra := 1
  states := 3 + 2
  machine := MaskedReset.machine Halve.machine (fun _ => true)
  cost := fun x => 2 * (x + 1) + 2
  run := fun x => by
    obtain ⟨k, hm⟩ := step_mask0 (Halve.run x) (fun _ => true) (fun _ _ => rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, rfl, rfl⟩
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]

theorem halve_cost (x : ℕ) : halveMap.cost x ≤ 4 * (x + 3) ^ 1 := by
  change 2 * (x + 1) + 2 ≤ _
  rw [pow_one]; omega

/-- The erase's port `↦ 1`, driver `↦ 0`, log `↦ 2`. -/
def zSlots : Fin (1 + 1 + 1) → Fin (2 + 1) := ![1, 0, 2]

theorem zSlots_inj : Function.Injective zSlots := by decide

/-- **`1^x ↦ 0^x`** as a word map. -/
def zerosMap : WordMap (fun x => List.replicate x false) where
  extra := 1
  states := 4
  machine := RecoveryFocus.machine zSlots (RecoveryScratchErase.resetMachine 1)
  cost := fun x => 2 * x + 4
  run := fun x => by
    have h := Step.of_ready (RecoveryScratchErase.erase_ready x 0 (fun _ : Fin 1 => []) (fun _ => by simp))
    have d := h.dock zSlots zSlots_inj (fun _ => 0) (unIn (2 + 1) x) (fun _ => rfl) (by
      intro j
      fin_cases j <;> rfl)
    refine ⟨_, _, d, ?_, ?_⟩
    · rw [show (⟨1, by omega⟩ : Fin (2 + 1)) = zSlots 0 from rfl, install_slot _ zSlots_inj]
      rfl
    · rw [show (⟨1, by omega⟩ : Fin (2 + 1)) = zSlots 0 from rfl, dockH_slot _ zSlots_inj]

theorem zeros_cost (x : ℕ) : zerosMap.cost x ≤ 4 * (x + 3) ^ 1 := by
  change 2 * x + 4 ≤ _
  rw [pow_one]; omega

/-! ## 3. `gateMembers liveᶜ`: splitter ; framed complement ; unwrap -/

def cSlots (i : Fin 13) : Fin (2 + 15) := Fin.castLE (by omega) (uSlots 2 i)

theorem cSlots_val (i : Fin 13) : (cSlots i).val = (uSlots 2 i).val := rfl

theorem cSlots_inj : Function.Injective cSlots := by
  intro x y h
  exact uSlots_inj 2 (Fin.ext (by have := congrArg Fin.val h; rwa [cSlots_val, cSlots_val] at this))

theorem cSlots_lt (i : Fin 13) : (cSlots i).val < 14 := by
  rw [cSlots_val, uSlots_val]
  have := i.isLt
  split_ifs <;> simp <;> omega

/-- The complement's slots: framed mask, framed complement, log. -/
def mSlots : Fin 3 → Fin (2 + 15) := ![⟨2, by omega⟩, ⟨14, by omega⟩, ⟨15, by omega⟩]
/-- The unwrap's slots: framed complement, output, log. -/
def vSlots : Fin 3 → Fin (2 + 15) := ![⟨14, by omega⟩, ⟨1, by omega⟩, ⟨16, by omega⟩]

theorem mSlots_inj : Function.Injective mSlots := by decide
theorem vSlots_inj : Function.Injective vSlots := by decide
theorem mSlots_ne0 : ∀ j, mSlots j ≠ ⟨0, by omega⟩ := by decide
theorem mSlots_ne1 : ∀ j, mSlots j ≠ ⟨1, by omega⟩ := by decide
theorem mSlots_ne16 : ∀ j, mSlots j ≠ ⟨16, by omega⟩ := by decide
theorem vSlots_ne0 : ∀ j, vSlots j ≠ ⟨0, by omega⟩ := by decide
theorem cSlots_five : cSlots ⟨2 + 3, by omega⟩ = ⟨2, by omega⟩ := by decide
theorem cSlots_zero : cSlots ⟨0, by omega⟩ = ⟨0, by omega⟩ := by decide

theorem mask_not (m : List Bool) : (m.map not).length = m.length := List.length_map _

/-- **The complement of the live mask** (`(fields a r 2).map not`). -/
def complWord (a : DecompositionAlgorithm) : WordStage a (fun r => (fields a r 2).map not) where
  extra := 15
  states := _
  machine := Composition.machine (Composition.machine
    (RecoveryFocus.machine cSlots PCJ45bee56da9f34d5a_RequestFields.machine)
    (RecoveryFocus.machine mSlots MatrixComplement.resetMachine))
    (RecoveryFocus.machine vSlots Streaming.machine)
  cost := fun r => 6 * (r.input a).length + 17 + 1 + (4 * (fields a r 2).length + 4) + 1 +
    (4 * ((fields a r 2).map not).length + 2)
  coefficient := 40
  degree := 1
  cost_le := by
    intro r
    have h := input_le_small a r
    have hf := field_le_input a r 2
    rw [frame_length] at hf
    rw [mask_not, pow_one]
    omega
  run := by
    intro r
    set m := fields a r 2 with hm
    have d1 := (PCJ45bee56da9f34d5a_RequestFields.request_run a r).dock cSlots cSlots_inj (fun _ => 0)
      (inBank (2 + 15) (Request.input a r)) (fun _ => rfl)
      (request_in a r _ cSlots (fun i => by rw [cSlots_val]; exact uSlots_zero 2 i))
    set H1 := dockH cSlots (fun _ => 0)
      (PCJ45bee56da9f34d5a_RequestFields.heads (PCJ45bee56da9f34d5a_RequestFields.values a r) 5) with hH1
    set A1 := install cSlots (inBank (2 + 15) (Request.input a r))
      (PCJ45bee56da9f34d5a_RequestFields.bank (PCJ45bee56da9f34d5a_RequestFields.values a r) 5) with hA1
    have ne : ∀ (k : ℕ) (hk : 14 ≤ k) (hk' : k < 2 + 15) (i : Fin 13), cSlots i ≠ ⟨k, hk'⟩ := by
      intro k hk hk' i h
      have := cSlots_lt i
      rw [h] at this
      simp at this
      omega
    obtain ⟨rc, hrc, hc0, hc1, hch, _⟩ := MatrixComplement.reset_run m [] (by simp)
    have w2 := (Step.of_run (p := MatrixComplement.resetMachine) hrc (funext hch) rfl).dock mSlots mSlots_inj H1 A1
      (by
        intro k
        fin_cases k
        · change H1 ⟨2, by omega⟩ = 0
          rw [← cSlots_five, hH1, dockH_slot _ cSlots_inj]
          exact LoopWords.heads_field _ 2
        · exact dockH_other _ _ _ _ (ne 14 (by omega) (by omega))
        · exact dockH_other _ _ _ _ (ne 15 (by omega) (by omega)))
      (by
        intro k
        fin_cases k
        · change A1 ⟨2, by omega⟩ = frame m
          rw [← cSlots_five, hA1, install_slot _ cSlots_inj]
          exact LoopWords.bank_field _ 2
        · change A1 ⟨14, by omega⟩ = []
          rw [hA1, install_other _ _ _ _ (ne 14 (by omega) (by omega))]
          rfl
        · change A1 ⟨15, by omega⟩ = []
          rw [hA1, install_other _ _ _ _ (ne 15 (by omega) (by omega))]
          rfl)
    set H2 := dockH mSlots H1 (fun _ => 0) with hH2
    set A2 := install mSlots A1 rc.final.tapes with hA2
    obtain ⟨ru, hru, hut, huh, _⟩ := UInputFields.unwrap_ready (m.map not)
    have w3 := (Step.of_run hru (funext huh) hut).dock vSlots vSlots_inj H2 A2
      (by
        intro k
        fin_cases k
        · change H2 (mSlots 1) = 0
          rw [hH2, dockH_slot _ mSlots_inj]
        · change H2 ⟨1, by omega⟩ = 0
          rw [hH2, dockH_other _ _ _ _ mSlots_ne1]
          rw [hH1, dockH_other _ _ _ _ (fun i h => by have := congrArg Fin.val h; rw [cSlots_val] at this; exact uSlots_ne1 2 i (Fin.ext this))]
        · change H2 ⟨16, by omega⟩ = 0
          rw [hH2, dockH_other _ _ _ _ mSlots_ne16, hH1,
            dockH_other _ _ _ _ (ne 16 (by omega) (by omega))])
      (by
        intro k
        fin_cases k
        · change A2 (mSlots 1) = frame (m.map not)
          rw [hA2, install_slot _ mSlots_inj]
          exact hc1
        · change A2 ⟨1, by omega⟩ = []
          rw [hA2, install_other _ _ _ _ mSlots_ne1]
          rw [hA1, install_other _ _ _ _ (fun i h => by have := congrArg Fin.val h; rw [cSlots_val] at this; exact uSlots_ne1 2 i (Fin.ext this))]
          rfl
        · change A2 ⟨16, by omega⟩ = []
          rw [hA2, install_other _ _ _ _ mSlots_ne16, hA1,
            install_other _ _ _ _ (ne 16 (by omega) (by omega))]
          rfl)
    refine ⟨_, _, (d1.seq w2).seq w3, ?_, ?_, ?_, ?_⟩
    · rw [install_other _ _ _ _ vSlots_ne0, hA2, install_other _ _ _ _ mSlots_ne0, hA1, ← cSlots_zero,
        install_slot _ cSlots_inj]
      change frame (PCJ45bee56da9f34d5a_RequestFields.word (PCJ45bee56da9f34d5a_RequestFields.values a r)) = _
      rw [PCJ45bee56da9f34d5a_RequestFields.word_values]
    · rw [dockH_other _ _ _ _ vSlots_ne0, hH2, dockH_other _ _ _ _ mSlots_ne0, hH1, ← cSlots_zero,
        dockH_slot _ cSlots_inj]
      rfl
    · rw [show (⟨1, by omega⟩ : Fin (2 + 15)) = vSlots 1 from rfl, install_slot _ vSlots_inj]
      rfl
    · rw [show (⟨1, by omega⟩ : Fin (2 + 15)) = vSlots 1 from rfl, dockH_slot _ vSlots_inj]

/-- The complemented mask IS `gateMembers liveᶜ`. -/
theorem compl_mask {q : ℕ} (occ : List (NearCubicWires.SupplierPipeline.SupportedNormalizedGate q)) (L : ℕ) :
    (CyclicChoice.mask occ L).map not = CloseoutRowsGateSupport.gateMembers (CyclicChoice.live occ L)ᶜ := by
  unfold CyclicChoice.mask CloseoutRowsGateSupport.gateMembers
  rw [List.map_ofFn]
  congr 1
  funext x
  simp

/-! ## 4. The nine words and the vector stage -/

section Words
variable (a : DecompositionAlgorithm)
open RowsConstruction RowsConstruction.BaseLayout

/-- `s = |liveᶜ|` (the pool arity), `s/2`, `(s+1)/2`. -/
abbrev sOf (r : Request) : ℕ := RowsInit.complCount a r

def hS : UnaryStage a (fun r => sOf a r / 2) := (RowsInit.complStage a).thenMapP halveMap 4 1 halve_cost
def hS1 : UnaryStage a (fun r => (sOf a r + 1) / 2) :=
  ((RowsInit.complStage a).thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)).thenMapP halveMap 4 1 halve_cost

def y0 : WordStage a (fun r => frame (SignedSortKey.binary ((sOf a r + 1) / 2) 0)) :=
  (hS1 a).thenWordP zeroWordMap 8 1 zero_cost
def y1 : WordStage a (fun r => frame (SignedSortKey.binary (sOf a r / 2) 0)) :=
  (hS a).thenWordP zeroWordMap 8 1 zero_cost
def y2 : WordStage a (fun r => List.replicate (loopCl r.q) false) :=
  wofEq (((qStage a).thenMapP (polyMap 1 2) (UnaryCalc.polyCoefficient 1 2) (1+1) (poly_cost 1 2)).thenWordP
    zerosMap 4 1 zeros_cost) (fun r => by simp [UnaryCalc.value, loopCl]; ring_nf)
def y3 : WordStage a (fun r => List.replicate (loopDl r.q) false) :=
  wofEq ((((qStage a).thenMapP (polyMap 1 4) (UnaryCalc.polyCoefficient 1 4) (1+1) (poly_cost 1 4)).thenMapP
    (plusMap 3) (2 * 3 + 4) 1 (plus_cost 3)).thenWordP zerosMap 4 1 zeros_cost)
    (fun r => by simp [UnaryCalc.value, loopDl]; ring_nf)
def y4 : WordStage a (fun r => CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a))ᶜ) :=
  wofEq (complWord a) (fun _ => compl_mask _ _)
def y5 : WordStage a (fun r => RepairSource.VerifierDecoding.CompareMachine.word r.q) :=
  (qStage a).thenWordP cmpWordMap 6 1 cmp_cost
def y6 : WordStage a (fun r => List.replicate (sOf a r / 2) true) := (hS a).toWord
def y7 : WordStage a (fun r => List.replicate ((sOf a r + 1) / 2) true) := (hS1 a).toWord
def y8 : WordStage a (fun r => List.replicate (sOf a r) true) := (RowsInit.complStage a).toWord

end Words

/-- **I6's small-class loop words**: aux 0, 1, 3, 4, 5, 6 on tapes 1–6; `1^(s/2)`, `1^((s+1)/2)`, `1^s` on 7–9. -/
def auxVec (a : DecompositionAlgorithm) :=
  (((((((((VecStage.nil a (fun _ _ => [])).snoc (y0 a)).snoc (y1 a)).snoc (y2 a)).snoc (y3 a)).snoc (y4 a)).snoc (y5 a)).snoc (y6 a)).snoc (y7 a)).snoc (y8 a)

end
end RowsInit.LoopAux
