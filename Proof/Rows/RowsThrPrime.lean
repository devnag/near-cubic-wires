import Proof.Packets.PacketsPrimeService
import Proof.Rows.RowsKeyTop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrPrime
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
noncomputable section

/-! ## 1. `TwoMax`: `1^x ↦ 1^(max 2 x)` -/

namespace TwoMax

/-- Tapes 0 the argument, 1 the output (both heads move together). States: 0 start, 1 one seen, 2 copying,
3 one more `true` to write, 4 halt. -/
def machine : NearCubicWires.LocalBitMultitape.Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q b =>
    if q.val = 0 then some (if b 0 then ⟨1, ![none, some true], ![.right, .right]⟩
      else ⟨3, ![none, some true], ![.right, .right]⟩)
    else if q.val = 1 then some (if b 0 then ⟨2, ![none, some true], ![.right, .right]⟩
      else ⟨4, ![none, some true], ![.stay, .stay]⟩)
    else if q.val = 2 then some (if b 0 then ⟨2, ![none, some true], ![.right, .right]⟩
      else ⟨4, ![none, none], ![.stay, .stay]⟩)
    else if q.val = 3 then some ⟨4, ![none, some true], ![.stay, .stay]⟩
    else none

def cfg (q : Fin 5) (x i o : ℕ) : Configuration 2 5 :=
  ⟨q, ![i, i], ![List.replicate x true, List.replicate o true]⟩

theorem s0t (x : ℕ) (hx : 0 < x) : step machine (cfg 0 x 0 0) = some (cfg 1 x 1 1) := by
  have hr : readTapeBit (List.replicate x true) 0 = true := read_replicate_true x 0 hx
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, writeTapeBit]

theorem s0f : step machine (cfg 0 0 0 0) = some (cfg 3 0 1 1) := by
  simp [step, machine, cfg, Configuration.scanned, readTapeBit]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, writeTapeBit]

theorem w11 : writeTapeBit [true] 1 true = [true, true] := by
  simp [writeTapeBit]

theorem r11 : readTapeBit [true] 1 = false := by
  simp [readTapeBit]

theorem s1t (x : ℕ) (hx : 1 < x) : step machine (cfg 1 x 1 1) = some (cfg 2 x 2 2) := by
  have hr : readTapeBit (List.replicate x true) 1 = true := read_replicate_true x 1 hx
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, w11]

theorem s1f : step machine (cfg 1 1 1 1) = some (cfg 4 1 1 2) := by
  simp [step, machine, cfg, Configuration.scanned, r11]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, w11]

theorem s2t (x i : ℕ) (hi : i < x) : step machine (cfg 2 x i i) = some (cfg 2 x (i + 1) (i + 1)) := by
  have hr : readTapeBit (List.replicate x true) i = true := read_replicate_true x i hi
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end_replicate]

theorem s2f (x : ℕ) : step machine (cfg 2 x x x) = some (cfg 4 x x x) := by
  have hr : readTapeBit (List.replicate x true) x = false := read_replicate_end x true
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s3 : step machine (cfg 3 0 1 1) = some (cfg 4 0 1 2) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, w11]

theorem copy (x : ℕ) : ∀ i, 2 ≤ i → i ≤ x → Timed machine (x - i) (cfg 2 x i i) (cfg 2 x x x) := by
  intro i hi hix
  induction h : x - i generalizing i with
  | zero =>
    have : i = x := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s2t x i (by omega))
    have t2 := ih (i + 1) (by omega) (by omega) (by omega)
    have t := t1.trans t2
    rw [show 1 + k = k + 1 by omega] at t
    exact t

/-- **`TwoMax.run`**: `1^x ↦ 1^(max 2 x)` in at most `x+2` steps; the argument is kept. -/
theorem run (x : ℕ) : ∃ H, Step machine (x + 2) ![0, 0] ![List.replicate x true, []] H
    ![List.replicate x true, List.replicate (max 2 x) true] := by
  have hc : ∀ y, (⟨machine.start, ![0, 0], ![List.replicate y true, []]⟩ : Configuration 2 5) = cfg 0 y 0 0 :=
    fun _ => rfl
  rcases Nat.lt_or_ge x 2 with hx | hx
  · rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
    · have t := (Timed.single (p := machine) (by simp [machine, cfg]) s0f).trans
        (Timed.single (p := machine) (by simp [machine, cfg]) s3)
      obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
      refine ⟨_, r, ?_, rfl, by rw [hf]; rfl, by omega⟩
      rw [hc]
      simpa using hr
    · have t := (Timed.single (p := machine) (by simp [machine, cfg]) (s0t 1 (by omega))).trans
        (Timed.single (p := machine) (by simp [machine, cfg]) s1f)
      obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
      have st : Step machine (1+1) ![0, 0] ![List.replicate 1 true, []] (cfg 4 1 1 2).heads
          ![List.replicate 1 true, List.replicate (max 2 1) true] := by
        refine ⟨r, ?_, by rw [hf], by rw [hf]; rfl, by omega⟩
        rw [hc]
        exact hr
      exact ⟨_, st.enlarge (by omega)⟩
  · have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s0t x (by omega))
    have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (s1t x (by omega))
    have t3 := copy x 2 (le_refl 2) hx
    have t4 := Timed.single (p := machine) (by simp [machine, cfg]) (s2f x)
    have t := ((t1.trans t2).trans t3).trans t4
    obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
    have hm : max 2 x = x := by omega
    have st : Step machine (1+1+(x-2)+1) ![0, 0] ![List.replicate x true, []] (cfg 4 x x x).heads
        ![List.replicate x true, List.replicate (max 2 x) true] := by
      refine ⟨r, ?_, by rw [hf], by rw [hf, hm]; rfl, by omega⟩
      rw [hc]
      exact hr
    exact ⟨_, st.enlarge (by omega)⟩

end TwoMax

/-! ## 2. The local stages, each a `Step` on its own bank with all exit heads `0` -/

theorem addCases_zero {m : Nat} (f : Fin m → ℕ) (hf : ∀ i, f i = 0) :
    (fun i => Fin.addCases (motive := fun _ => ℕ) (n := 1) f (fun _ => 0) i) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [hf]
  · simp

/-- The unary → `CompareMachine.word` counter (pinned `DriverAtoms.counter_run` + `step_of_clock`). -/
theorem counter_step (n : Nat) : ∃ out,
    Step NearCubicWires.RepairSource.ProjectionNormalization.Counter.machine
      (NearCubicWires.RepairSource.ProjectionNormalization.Counter.budget n) (fun _ => 0)
      (NearCubicWires.RepairSource.ProjectionNormalization.Counter.input n) (fun _ => 0) out ∧
      out 0 = List.replicate n true ∧ out 2 = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word n := by
  obtain ⟨out, h, h0, h2⟩ := NearCubicWires.RepairSource.ProjectionNormalization.DriverAtoms.counter_run n
  exact ⟨out, NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit.step_of_clock h, h0, h2⟩

/-- One head move right on one tape. -/
def bump : NearCubicWires.LocalBitMultitape.Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => decide (s = 1)
  rule := fun s _ => if s = 0 then some ⟨1, fun _ => none, fun _ => .right⟩ else none

theorem bump_step (h : Nat) (t : List Bool) :
    Step bump 1 (fun _ => h) (fun _ => t) (fun _ => h+1) (fun _ => t) := by
  have hs : step bump (⟨bump.start, fun _ => h, fun _ => t⟩ : Configuration 1 2) =
      some ⟨1, fun _ => h+1, fun _ => t⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      rfl
    · rfl
  obtain ⟨r, hr, hf, _⟩ := (Timed.single (by rfl) hs).run rfl
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

/-- The binary → template converter, all heads returned to `0` (log `0^R`). -/
theorem bin_step (w p R : Nat) (hp : p < 2^w)
    (hR : NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.budget 0 w p ≤ R) :
    ∃ out : Fin 13 → List Bool,
      Step (MaskedReset.machine NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.machine (fun _ => true))
        (2*NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.budget 0 w p+2) (fun _ => 0)
        (Fin.addCases (NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.input [] [] w p)
          (fun _ : Fin 1 => List.replicate R false)) (fun _ => 0)
        (Fin.addCases out (fun _ : Fin 1 => List.replicate R false)) ∧
      out 0 = KeyStep.fb w p ∧ out 12 = UnaryTemplate.tape p := by
  obtain ⟨r, hrun, hsteps, h12, _, _, h0, _, _⟩ :=
    NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.index_run [] [] w p hp
  simp only [List.length_nil] at hrun hsteps
  have hstep : Step NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.machine
      (NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.budget 0 w p) (fun _ => 0)
      (NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.input [] [] w p)
      r.final.heads r.final.tapes := ⟨r, hrun, rfl, rfl, hsteps⟩
  have hm := hstep.mask (fun _ => true) (fun _ _ => rfl) (cap := R) hR
  refine ⟨r.final.tapes, (hm.congr_in (addCases_zero _ (fun _ => rfl)) rfl).congr
    (addCases_zero _ (fun _ => by simp)) rfl, ?_, h12⟩
  rw [h0]
  simp [KeyStep.fb]

/-- `1^next` for PG's `nextPrimeMap`, all heads returned to `0` (log `0^R`). -/
theorem next_step (c p R : Nat) (hR : NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.cost c p ≤ R) :
    ∃ out : Fin (3 + NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.extra) → List Bool,
      Step (MaskedReset.machine NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.machine (fun _ => true))
        (2*NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.cost c p+2) (fun _ => 0)
        (Fin.addCases (NearCubicWires.PacketsGlue.RequestMeta.unIn2
            (3 + NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.extra) c p)
          (fun _ : Fin 1 => List.replicate R false)) (fun _ => 0)
        (Fin.addCases out (fun _ : Fin 1 => List.replicate R false)) ∧
      out ⟨2, by omega⟩ = List.replicate (NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p) true := by
  obtain ⟨H', A', h, h2, _⟩ := NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.run c p
  have hm := h.mask (fun _ => true) (fun _ _ => rfl) (cap := R) hR
  exact ⟨A', (hm.congr_in (addCases_zero _ (fun _ => rfl)) rfl).congr
    (addCases_zero _ (fun _ => by simp)) rfl, h2⟩

/-- `1^(max 2 x)`, all heads returned to `0` (log `0^R`). -/
theorem two_step (x R : Nat) (hR : x + 2 ≤ R) :
    Step (MaskedReset.machine TwoMax.machine (fun _ => true)) (2*(x+2)+2) (fun _ => 0)
      (Fin.addCases ![List.replicate x true, []] (fun _ : Fin 1 => List.replicate R false)) (fun _ => 0)
      (Fin.addCases ![List.replicate x true, List.replicate (max 2 x) true]
        (fun _ : Fin 1 => List.replicate R false)) := by
  obtain ⟨H, h⟩ := TwoMax.run x
  have hm := h.mask (fun _ => true) (fun i _ => by fin_cases i <;> rfl) (cap := R) hR
  exact (hm.congr_in (addCases_zero _ (fun i => by fin_cases i <;> rfl)) rfl).congr
    (addCases_zero _ (fun _ => by simp)) rfl

/-! ## 3. The 40-tape local bank and the raw pipeline

Ports: 0 the digit (`fb w p`), 1 the cutoff `1^c`, 2 the ruler `1^w`, 3 `[true]`; 4–39 scratch (entry `[]`,
except the four logs 18, 33, 34, 39 and the counter scratch 38, entry `0^R`). -/

abbrev PT : Nat := 40

def psIn (w c p R : Nat) : Fin PT → List Bool := fun i =>
  if i.val = 0 then KeyStep.fb w p else if i.val = 1 then List.replicate c true
  else if i.val = 2 then List.replicate w true else if i.val = 3 then [true]
  else if i.val = 18 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 38 ∨ i.val = 39 then List.replicate R false else []

def s1 : Fin 4 → Fin PT := ![2, 4, 5, 6]
def s2 : Fin (13+1) → Fin PT := ![0, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
def s3 : Fin 4 → Fin PT := ![3, 17, 19, 20]
def s4 : Fin 4 → Fin PT := ![1, 21, 22, 23]
def s5 : Fin (3 + NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.extra + 1) → Fin PT :=
  ![22, 19, 24, 25, 26, 27, 28, 29, 30, 31, 39]
def s6 : Fin (2+1) → Fin PT := ![24, 32, 33]
def s7 : Fin 2 → Fin PT := ![0, 34]
def s8 : Fin 4 → Fin PT := ![32, 35, 36, 37]
def s9 : Fin 1 → Fin PT := ![36]
def s10 : Fin 4 → Fin PT := ![0, 38, 32, 36]

theorem s1_inj : Function.Injective s1 := by decide
theorem s2_inj : Function.Injective s2 := by decide
theorem s3_inj : Function.Injective s3 := by decide
theorem s4_inj : Function.Injective s4 := by decide
theorem s5_inj : Function.Injective s5 := by decide
theorem s6_inj : Function.Injective s6 := by decide
theorem s7_inj : Function.Injective s7 := by decide
theorem s8_inj : Function.Injective s8 := by decide
theorem s9_inj : Function.Injective s9 := by decide
theorem s10_inj : Function.Injective s10 := by decide

def m1 := RecoveryFocus.machine s1 NearCubicWires.RepairOrdinary.ClockUnarySum.machine
def m2 := RecoveryFocus.machine s2
  (MaskedReset.machine NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.machine (fun _ => true))
def m3 := RecoveryFocus.machine s3 NearCubicWires.RepairOrdinary.ClockUnaryProduct.machine
def m4 := RecoveryFocus.machine s4 NearCubicWires.RepairOrdinary.ClockUnarySum.machine
def m5 := RecoveryFocus.machine s5
  (MaskedReset.machine NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.machine (fun _ => true))
def m6 := RecoveryFocus.machine s6 (MaskedReset.machine TwoMax.machine (fun _ => true))
def m7 := RecoveryFocus.machine s7 (MaskedReset.machine FinalPrimeCursor.clearMachine (fun _ => true))
def m8 := RecoveryFocus.machine s8 NearCubicWires.RepairSource.ProjectionNormalization.Counter.machine
def m9 := RecoveryFocus.machine s9 bump
def m10 := RecoveryFocus.machine s10 PCJ45bee56da9f34d5a_CountFlags.machine

/-- **The raw prime pipeline** (one fixed machine). -/
def psRaw := Composition.machine m1 (Composition.machine m2 (Composition.machine m3 (Composition.machine m4
  (Composition.machine m5 (Composition.machine m6 (Composition.machine m7 (Composition.machine m8
    (Composition.machine m9 m10))))))))

/-- The prime of row `j+1`'s key: the next prime `≤ c`, or `2` past the last one. -/
def nextP (c p : Nat) : Nat := max 2 (NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p)

def psCost (w c p : Nat) : Nat :=
  (2*w+6)+1+((2*NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.budget 0 w p+2)+1+
  ((2*(1*(2*p+3)+2)+2)+1+((2*c+6)+1+
  ((2*NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.cost c p+2)+1+
  ((2*(NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p+2)+2)+1+((2*(2*w+1)+2)+1+
  (NearCubicWires.RepairSource.ProjectionNormalization.Counter.budget (nextP c p)+1+
  (1+1+PCJ45bee56da9f34d5a_CountFlags.budget (nextP c p) w))))))))

theorem psDock {t s n : Nat} {p : NearCubicWires.LocalBitMultitape.Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin t → Fin PT) (hi : Function.Injective sl)
    (A : Fin PT → List Bool) (hA : ∀ j, A (sl j) = tin j) :
    Step (RecoveryFocus.machine sl p) n (fun _ => 0) A (fun _ => 0) (install sl A tout) :=
  (h.dock sl hi _ A (fun _ => rfl) hA).congr
    (NearCubicWires.ExtDecompositionBatch.dockH_existing _ _ _ (fun _ => rfl)) rfl

/-- **The raw pipeline's run.** Port 0 ends as `fb w (nextP c p)`; ports 1–3 are kept. -/
theorem ps_raw (w c p R : Nat) (hp : p < 2^w) (hq : nextP c p < 2^w)
    (h1 : NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.budget 0 w p ≤ R)
    (h2 : NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.cost c p ≤ R)
    (h3 : NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p + 2 ≤ R) (h4 : 2*w+1 ≤ R) :
    ∃ (H' : Fin PT → ℕ) (A' : Fin PT → List Bool), Step psRaw (psCost w c p) (fun _ => 0) (psIn w c p R) H' A' ∧
      A' 0 = KeyStep.fb w (nextP c p) ∧ A' 1 = List.replicate c true ∧ A' 2 = List.replicate w true ∧
      A' 3 = [true] := by
  set A0 := psIn w c p R with hA0
  -- stage 1: copy the ruler (ports 2 → 5)
  have d1 := psDock (NearCubicWires.BlockPlatform.UnaryCalc.copy_step w) s1 s1_inj A0
    (fun j => by fin_cases j <;> rfl)
  set A1 := install s1 A0 ![List.replicate w true, [], List.replicate w true, List.replicate (w+2) false] with hA1
  have o1 : ∀ x : Fin PT, (∀ j, s1 j ≠ x) → A1 x = A0 x := fun x hx => install_other _ _ _ x hx
  have a1_5 : A1 5 = List.replicate w true := install_slot _ s1_inj _ _ 2
  -- stage 2: `fb w p ↦ tape p` (port 17)
  obtain ⟨o2v, st2, o2_0, o2_12⟩ := bin_step w p R hp h1
  have d2 := psDock st2 s2 s2_inj A1 (fun j => by
    fin_cases j
    · show A1 0 = NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.input [] [] w p 0
      rw [o1 0 (by decide)]
      simp [hA0, psIn, NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.input, KeyStep.fb]
    · show A1 7 = _; rw [o1 7 (by decide)]; rfl
    · show A1 8 = _; rw [o1 8 (by decide)]; rfl
    · show A1 5 = _; rw [a1_5]; rfl
    · show A1 9 = _; rw [o1 9 (by decide)]; rfl
    · show A1 10 = _; rw [o1 10 (by decide)]; rfl
    · show A1 11 = _; rw [o1 11 (by decide)]; rfl
    · show A1 12 = _; rw [o1 12 (by decide)]; rfl
    · show A1 13 = _; rw [o1 13 (by decide)]; rfl
    · show A1 14 = _; rw [o1 14 (by decide)]; rfl
    · show A1 15 = _; rw [o1 15 (by decide)]; rfl
    · show A1 16 = _; rw [o1 16 (by decide)]; rfl
    · show A1 17 = _; rw [o1 17 (by decide)]; rfl
    · show A1 18 = _; rw [o1 18 (by decide)]; rfl)
  set A2 := install s2 A1 (Fin.addCases o2v (fun _ : Fin 1 => List.replicate R false)) with hA2
  have o2 : ∀ x : Fin PT, (∀ j, s2 j ≠ x) → A2 x = A1 x := fun x hx => install_other _ _ _ x hx
  have a2_0 : A2 0 = KeyStep.fb w p := (install_slot _ s2_inj _ _ 0).trans o2_0
  have a2_17 : A2 17 = UnaryTemplate.tape p := (install_slot _ s2_inj _ _ 12).trans o2_12
  -- stage 3: `tape p ↦ 1^p` (port 19)
  have d3 := psDock (NearCubicWires.PacketsGlue.RequestMeta.prod_step 1 p) s3 s3_inj A2 (fun j => by
    fin_cases j
    · show A2 3 = _; rw [o2 3 (by decide), o1 3 (by decide)]; rfl
    · show A2 17 = _; rw [a2_17]; rfl
    · show A2 19 = _; rw [o2 19 (by decide), o1 19 (by decide)]; rfl
    · show A2 20 = _; rw [o2 20 (by decide), o1 20 (by decide)]; rfl)
  set A3 := install s3 A2 ![List.replicate 1 true, UnaryTemplate.tape p, List.replicate (1*p) true,
    List.replicate (1*(2*p+3)+2) false] with hA3
  have o3 : ∀ x : Fin PT, (∀ j, s3 j ≠ x) → A3 x = A2 x := fun x hx => install_other _ _ _ x hx
  have a3_19 : A3 19 = List.replicate p true := by
    rw [show A3 19 = List.replicate (1*p) true from install_slot _ s3_inj _ _ 2, Nat.one_mul]
  have a3_3 : A3 3 = [true] := install_slot _ s3_inj _ _ 0
  -- stage 4: copy the cutoff (ports 1 → 22)
  have d4 := psDock (NearCubicWires.BlockPlatform.UnaryCalc.copy_step c) s4 s4_inj A3 (fun j => by
    fin_cases j
    · show A3 1 = _; rw [o3 1 (by decide), o2 1 (by decide), o1 1 (by decide)]; rfl
    · show A3 21 = _; rw [o3 21 (by decide), o2 21 (by decide), o1 21 (by decide)]; rfl
    · show A3 22 = _; rw [o3 22 (by decide), o2 22 (by decide), o1 22 (by decide)]; rfl
    · show A3 23 = _; rw [o3 23 (by decide), o2 23 (by decide), o1 23 (by decide)]; rfl)
  set A4 := install s4 A3 ![List.replicate c true, [], List.replicate c true, List.replicate (c+2) false] with hA4
  have o4 : ∀ x : Fin PT, (∀ j, s4 j ≠ x) → A4 x = A3 x := fun x hx => install_other _ _ _ x hx
  have a4_22 : A4 22 = List.replicate c true := install_slot _ s4_inj _ _ 2
  have a4_1 : A4 1 = List.replicate c true := install_slot _ s4_inj _ _ 0
  -- stage 5: `1^next` (port 24)
  obtain ⟨o5v, st5, o5_2⟩ := next_step c p R h2
  have d5 := psDock st5 s5 s5_inj A4 (fun j => by
    fin_cases j
    · show A4 22 = _; rw [a4_22]; rfl
    · show A4 19 = _; rw [o4 19 (by decide), a3_19]; rfl
    · show A4 24 = _; rw [o4 24 (by decide), o3 24 (by decide), o2 24 (by decide), o1 24 (by decide)]; rfl
    · show A4 25 = _; rw [o4 25 (by decide), o3 25 (by decide), o2 25 (by decide), o1 25 (by decide)]; rfl
    · show A4 26 = _; rw [o4 26 (by decide), o3 26 (by decide), o2 26 (by decide), o1 26 (by decide)]; rfl
    · show A4 27 = _; rw [o4 27 (by decide), o3 27 (by decide), o2 27 (by decide), o1 27 (by decide)]; rfl
    · show A4 28 = _; rw [o4 28 (by decide), o3 28 (by decide), o2 28 (by decide), o1 28 (by decide)]; rfl
    · show A4 29 = _; rw [o4 29 (by decide), o3 29 (by decide), o2 29 (by decide), o1 29 (by decide)]; rfl
    · show A4 30 = _; rw [o4 30 (by decide), o3 30 (by decide), o2 30 (by decide), o1 30 (by decide)]; rfl
    · show A4 31 = _; rw [o4 31 (by decide), o3 31 (by decide), o2 31 (by decide), o1 31 (by decide)]; rfl
    · show A4 39 = _; rw [o4 39 (by decide), o3 39 (by decide), o2 39 (by decide), o1 39 (by decide)]; rfl)
  set A5 := install s5 A4 (Fin.addCases o5v (fun _ : Fin 1 => List.replicate R false)) with hA5
  have o5 : ∀ x : Fin PT, (∀ j, s5 j ≠ x) → A5 x = A4 x := fun x hx => install_other _ _ _ x hx
  have a5_24 : A5 24 = List.replicate (NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p) true :=
    (install_slot _ s5_inj _ _ 2).trans o5_2
  -- stage 6: `1^(max 2 next)` (port 32)
  have d6 := psDock (two_step (NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p) R h3) s6 s6_inj A5
    (fun j => by
      fin_cases j
      · show A5 24 = _; rw [a5_24]; rfl
      · show A5 32 = _
        rw [o5 32 (by decide), o4 32 (by decide), o3 32 (by decide), o2 32 (by decide), o1 32 (by decide)]; rfl
      · show A5 33 = _
        rw [o5 33 (by decide), o4 33 (by decide), o3 33 (by decide), o2 33 (by decide), o1 33 (by decide)]; rfl)
  set A6 := install s6 A5 (Fin.addCases ![List.replicate (NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p) true,
    List.replicate (nextP c p) true] (fun _ : Fin 1 => List.replicate R false)) with hA6
  have o6 : ∀ x : Fin PT, (∀ j, s6 j ≠ x) → A6 x = A5 x := fun x hx => install_other _ _ _ x hx
  have a6_32 : A6 32 = List.replicate (nextP c p) true := install_slot _ s6_inj _ _ 1
  -- stage 7: `fb w p ↦ fb w 0` (port 0)
  have d7 := psDock (KeyStep.clr_local w p R h4) s7 s7_inj A6 (fun j => by
    fin_cases j
    · show A6 0 = _; rw [o6 0 (by decide), o5 0 (by decide), o4 0 (by decide), o3 0 (by decide), a2_0]; rfl
    · show A6 34 = _
      rw [o6 34 (by decide), o5 34 (by decide), o4 34 (by decide), o3 34 (by decide), o2 34 (by decide),
        o1 34 (by decide)]; rfl)
  set A7 := install s7 A6 ![KeyStep.fb w 0, List.replicate R false] with hA7
  have o7 : ∀ x : Fin PT, (∀ j, s7 j ≠ x) → A7 x = A6 x := fun x hx => install_other _ _ _ x hx
  have a7_0 : A7 0 = KeyStep.fb w 0 := install_slot _ s7_inj _ _ 0
  -- stage 8: the loop word (port 36)
  obtain ⟨o8v, st8, o8_0, o8_2⟩ := counter_step (nextP c p)
  have d8 := psDock st8 s8 s8_inj A7 (fun j => by
    fin_cases j
    · show A7 32 = _; rw [o7 32 (by decide), a6_32]; rfl
    · show A7 35 = _
      rw [o7 35 (by decide), o6 35 (by decide), o5 35 (by decide), o4 35 (by decide), o3 35 (by decide),
        o2 35 (by decide), o1 35 (by decide)]; rfl
    · show A7 36 = _
      rw [o7 36 (by decide), o6 36 (by decide), o5 36 (by decide), o4 36 (by decide), o3 36 (by decide),
        o2 36 (by decide), o1 36 (by decide)]; rfl
    · show A7 37 = _
      rw [o7 37 (by decide), o6 37 (by decide), o5 37 (by decide), o4 37 (by decide), o3 37 (by decide),
        o2 37 (by decide), o1 37 (by decide)]; rfl)
  set A8 := install s8 A7 o8v with hA8
  have o8 : ∀ x : Fin PT, (∀ j, s8 j ≠ x) → A8 x = A7 x := fun x hx => install_other _ _ _ x hx
  have a8_32 : A8 32 = List.replicate (nextP c p) true := (install_slot _ s8_inj _ _ 0).trans o8_0
  have a8_36 : A8 36 = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word (nextP c p) :=
    (install_slot _ s8_inj _ _ 2).trans o8_2
  -- stage 9: the word's head to `1`
  have d9 := (bump_step 0 (A8 36)).dock s9 s9_inj (fun _ => 0) A8 (fun _ => rfl) (fun j => by fin_cases j; rfl)
  have e9 : install s9 A8 (fun _ => A8 36) = A8 := install_existing _ _ _ (fun j => by fin_cases j; rfl)
  rw [e9] at d9
  set H9 := dockH s9 (fun _ => 0) (fun _ => 0+1) with hH9
  have h9 : ∀ x : Fin PT, x ≠ 36 → H9 x = 0 := fun x hx => dockH_other _ _ _ x (fun j he => by
    fin_cases j; exact hx he.symm)
  have h9_36 : H9 36 = 1 := dockH_slot _ s9_inj _ _ 0
  -- stage 10: `fb w 0 ↦ fb w p''` (port 0)
  have hcf := PCJ45bee56da9f34d5a_CountFlags.run (List.replicate (nextP c p) true) [] w R
    (by rw [List.length_replicate]; exact hq) h4
  rw [List.length_replicate, List.count_replicate_self, List.append_nil] at hcf
  have d10 := hcf.dock s10 s10_inj H9 A8 (fun j => by
    fin_cases j
    · exact h9 0 (by decide)
    · exact h9 38 (by decide)
    · exact h9 32 (by decide)
    · exact h9_36) (fun j => by
    fin_cases j
    · show A8 0 = _; rw [o8 0 (by decide), a7_0]; rfl
    · show A8 38 = _
      rw [o8 38 (by decide), o7 38 (by decide), o6 38 (by decide), o5 38 (by decide), o4 38 (by decide),
        o3 38 (by decide), o2 38 (by decide), o1 38 (by decide)]; rfl
    · show A8 32 = _; rw [a8_32]; rfl
    · show A8 36 = _; rw [a8_36]; rfl)
  refine ⟨_, _, d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq (d8.seq (d9.seq d10)))))))), ?_, ?_, ?_, ?_⟩
  · exact install_slot _ s10_inj _ _ 0
  · rw [install_other _ _ _ 1 (by decide), o8 1 (by decide), o7 1 (by decide), o6 1 (by decide),
      o5 1 (by decide), a4_1]
  · rw [install_other _ _ _ 2 (by decide), o8 2 (by decide), o7 2 (by decide), o6 2 (by decide),
      o5 2 (by decide), o4 2 (by decide), o3 2 (by decide), o2 2 (by decide),
      show A1 2 = List.replicate w true from install_slot _ s1_inj _ _ 0]
  · rw [install_other _ _ _ 3 (by decide), o8 3 (by decide), o7 3 (by decide), o6 3 (by decide),
      o5 3 (by decide), o4 3 (by decide), a3_3]

/-! ## 4. The scrubbed prime stage: `psBank p ↦ psBank p''` exactly -/

/-- The scratch set: every port from 4 on. -/
def psS : Fin PT → Bool := fun i => decide (4 ≤ i.val)

def psMachine := NearCubicWires.BlockPlatform.Scrub.machine psRaw (fun _ => true) psS

/-- The stage's bank at a digit value `d`: the scratch at `0^R`. -/
def psBank (w c d R : Nat) : Fin PT → List Bool := fun i =>
  if i.val = 0 then KeyStep.fb w d else if i.val = 1 then List.replicate c true
  else if i.val = 2 then List.replicate w true else if i.val = 3 then [true] else List.replicate R false

theorem blank_psIn (w c p R : Nat) :
    NearCubicWires.BlockPlatform.Scrub.blank psS (psIn w c p R) R = psBank w c p R := by
  funext i
  simp only [NearCubicWires.BlockPlatform.Scrub.blank, psS, psIn, psBank]
  by_cases h0 : i.val = 0
  · simp [h0]
  · by_cases h1 : i.val = 1
    · simp [h1]
    · by_cases h2 : i.val = 2
      · simp [h2]
      · by_cases h3 : i.val = 3
        · simp [h3]
        · have h4 : 4 ≤ i.val := by omega
          simp [h0, h1, h2, h3, h4]

theorem scrub_heads_zero :
    NearCubicWires.BlockPlatform.Scrub.heads (t := PT) (fun _ => 0) = fun _ => 0 := by
  funext i
  refine NearCubicWires.BlockPlatform.Scrub.cover (t := PT)
    (motive := fun i => NearCubicWires.BlockPlatform.Scrub.heads (t := PT) (fun _ => 0) i = 0)
    (fun j => by simp) (by simp) (by simp) i

/-- **The prime stage's run.** From `psBank p` to `psBank (nextP c p)`, all heads `0`, the scrub's log `0^L` and
driver `1^R` kept: row `j+1`'s prime is written on port 0 and nothing else changes. -/
theorem ps_step (w c p R L : Nat) (hp : p < 2^w) (hq : nextP c p < 2^w) (hR : psCost w c p + 1 ≤ R)
    (hL : R + 1 ≤ L) :
    Step psMachine (2*psCost w c p+2+1+(2*R+4)) (fun _ => 0)
      (NearCubicWires.BlockPlatform.Scrub.bank (psBank w c p R) R L) (fun _ => 0)
      (NearCubicWires.BlockPlatform.Scrub.bank (psBank w c (nextP c p) R) R L) := by
  have e1 : NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.budget 0 w p ≤ R := by
    unfold psCost at hR; omega
  have e2 : NearCubicWires.PacketsGlue.RequestMeta.nextPrimeMap.cost c p ≤ R := by
    unfold psCost at hR; omega
  have e3 : NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p + 2 ≤ R := by
    unfold psCost at hR; omega
  have e4 : 2*w+1 ≤ R := by
    unfold psCost at hR; omega
  obtain ⟨H', A', h, a0, a1, a2, a3⟩ := ps_raw w c p R hp hq e1 e2 e3 e4
  have hc := NearCubicWires.BlockPlatform.Scrub.cleared_entry h psS R (fun i hi => by
    simp only [psS, decide_eq_true_eq] at hi
    simp only [psIn]
    have h0 : i.val ≠ 0 := by omega
    have h1 : i.val ≠ 1 := by omega
    have h2 : i.val ≠ 2 := by omega
    have h3 : i.val ≠ 3 := by omega
    simp only [h0, h1, h2, h3, if_false]
    split
    · exact ⟨R, le_refl R, rfl⟩
    · exact ⟨0, Nat.zero_le R, rfl⟩)
  have hlen : ∀ i : Fin PT, psS i = true → (psBank w c (nextP c p) R i).length ≤ R ∧
      psBank w c p R i = List.replicate R false ∧ psBank w c (nextP c p) R i = List.replicate R false := by
    intro i hi
    have h4 : 4 ≤ i.val := by simpa [psS] using hi
    have h0 : i.val ≠ 0 := by omega
    have h1 : i.val ≠ 1 := by omega
    have h2 : i.val ≠ 2 := by omega
    have h3 : i.val ≠ 3 := by omega
    simp [psBank, h0, h1, h2, h3]
  have hs := NearCubicWires.BlockPlatform.Scrub.step_into hc (fun _ => true) psS R L (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun i hi => by rw [blank_psIn, (hlen i hi).2.1, List.length_replicate])
    (by omega) hL (G := fun _ => 0) (B := psBank w c (nextP c p) R)
    (fun i hi => by
      have hi' : i.val < 4 := by
        by_contra hc'
        have : psS i = true := by simp [psS]; omega
        rw [this] at hi
        exact Bool.noConfusion hi
      rw [hi, if_neg (by simp), show ZeroPadding.pad 0 (A' i) = A' i by simp [ZeroPadding.pad]]
      obtain ⟨k, hk⟩ := i
      simp only at hi'
      interval_cases k
      · exact a0
      · exact a1
      · exact a2
      · exact a3)
    (fun i hi => (hlen i hi).2.2)
    (fun i hi => by simp at hi) (fun _ _ => rfl)
  rw [blank_psIn, scrub_heads_zero] at hs
  exact hs

end
end RowsConstruction.ThrPrime
