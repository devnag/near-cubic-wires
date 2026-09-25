import Proof.Packets.PacketsFieldWidth

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.FrameUnary
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

/-- Tape 0 `1^b`, tape 1 the output `frame (1^b)`. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q x =>
    if q.val = 0 then some (if x 0 then ⟨1, ![none, some true], ![.stay, .right]⟩
      else ⟨2, ![none, some false], ![.stay, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, some true], ![.right, .right]⟩
    else none

def cfg (q : Fin 3) (b i : ℕ) (o : List Bool) (ho : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, ho], ![List.replicate b true, o]⟩

theorem s0t (b i : ℕ) (hi : i < b) : step machine (cfg 0 b i (List.replicate (2 * i) true) (2 * i)) =
    some (cfg 1 b i (List.replicate (2 * i + 1) true) (2 * i + 1)) := by
  have hr : readTapeBit (List.replicate b true) i = true := read_replicate_true b i hi
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s1 (b i : ℕ) : step machine (cfg 1 b i (List.replicate (2 * i + 1) true) (2 * i + 1)) =
    some (cfg 0 b (i + 1) (List.replicate (2 * (i + 1)) true) (2 * (i + 1))) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]; omega
  · funext k; fin_cases k <;> simp [applyAction]; omega

theorem s0f (b : ℕ) : step machine (cfg 0 b b (List.replicate (2 * b) true) (2 * b)) =
    some (cfg 2 b b (List.replicate (2 * b) true ++ [false]) (2 * b)) := by
  have hr : readTapeBit (List.replicate b true) b = false := read_replicate_end b true
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]
    have := Streaming.write_append (List.replicate (2 * b) true) false
    simpa using this

theorem loop (b : ℕ) : ∀ i, i ≤ b →
    Timed machine (2 * (b - i)) (cfg 0 b i (List.replicate (2 * i) true) (2 * i))
      (cfg 0 b b (List.replicate (2 * b) true) (2 * b)) := by
  intro i hi
  induction h : b - i generalizing i with
  | zero =>
    have : i = b := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s0t b i (by omega))
    have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (s1 b i)
    have t3 := ih (i + 1) (by omega) (by omega)
    have t := (t1.trans t2).trans t3
    rw [show 1 + 1 + 2 * k = 2 * (k + 1) by omega] at t
    exact t

theorem frame_rep (b : ℕ) : RepairOrdinary.frame (List.replicate b true) = List.replicate (2 * b) true ++ [false] := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [List.replicate_succ, RepairOrdinary.frame, ih, show 2 * (b + 1) = 2 * b + 1 + 1 by omega,
      List.replicate_succ, List.replicate_succ]
    simp

theorem run (b : ℕ) : ∃ H, Step machine (2 * b + 1) ![0, 0] ![List.replicate b true, []] H
    ![List.replicate b true, RepairOrdinary.frame (List.replicate b true)] := by
  have t1 := loop b 0 (by omega)
  have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (s0f b)
  obtain ⟨r, hr, hf, hs⟩ := (t1.trans t2).run (by simp [machine, cfg])
  refine ⟨_, r, ?_, rfl, ?_, by omega⟩
  · have hc : (⟨machine.start, ![0, 0], ![List.replicate b true, []]⟩ : Configuration 2 3) =
        cfg 0 b 0 (List.replicate (2 * 0) true) (2 * 0) := rfl
    rw [hc]
    simpa using hr
  · rw [hf, frame_rep]; rfl

end NearCubicWires.PacketsGlue.FrameUnary

namespace NearCubicWires.PacketsGlue.CmpWord
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

/-- Tape 0 `1^n`, tape 1 the output `false :: 1^n`. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q x =>
    if q.val = 0 then some ⟨1, ![none, some false], ![.stay, .right]⟩
    else if q.val = 1 then some (if x 0 then ⟨1, ![none, some true], ![.right, .right]⟩
      else ⟨2, ![none, none], ![.stay, .stay]⟩)
    else none

def cfg (q : Fin 3) (n i : ℕ) (o : List Bool) (ho : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, ho], ![List.replicate n true, o]⟩

theorem s0 (n : ℕ) : step machine (cfg 0 n 0 [] 0) = some (cfg 1 n 0 [false] 1) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, writeTapeBit]

theorem s1t (n i : ℕ) (hi : i < n) : step machine (cfg 1 n i (false :: List.replicate i true) (i + 1)) =
    some (cfg 1 n (i + 1) (false :: List.replicate (i + 1) true) (i + 1 + 1)) := by
  have hr : readTapeBit (List.replicate n true) i = true := read_replicate_true n i hi
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · have h1 : writeTapeBit (false :: List.replicate i true) (i + 1) true = false :: List.replicate (i + 1) true := by
      have := Streaming.write_append (false :: List.replicate i true) true
      simp only [List.length_cons, List.length_replicate] at this
      rw [this, List.replicate_succ']; rfl
    funext k; fin_cases k
    · simp [applyAction]
    · simp only [applyAction]
      simp [h1]

theorem s1f (n : ℕ) : step machine (cfg 1 n n (false :: List.replicate n true) (n + 1)) =
    some (cfg 2 n n (false :: List.replicate n true) (n + 1)) := by
  have hr : readTapeBit (List.replicate n true) n = false := read_replicate_end n true
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem loop (n : ℕ) : ∀ i, i ≤ n →
    Timed machine (n - i) (cfg 1 n i (false :: List.replicate i true) (i + 1))
      (cfg 1 n n (false :: List.replicate n true) (n + 1)) := by
  intro i hi
  induction h : n - i generalizing i with
  | zero =>
    have : i = n := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s1t n i (by omega))
    have t2 := ih (i + 1) (by omega) (by omega)
    have t := t1.trans t2
    rw [show 1 + k = k + 1 by omega] at t
    exact t

theorem run (n : ℕ) : ∃ H, Step machine (n + 2) ![0, 0] ![List.replicate n true, []] H
    ![List.replicate n true, false :: List.replicate n true] := by
  have t0 := Timed.single (p := machine) (by simp [machine, cfg]) (s0 n)
  have t1 := loop n 0 (by omega)
  have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (s1f n)
  obtain ⟨r, hr, hf, hs⟩ := ((t0.trans t1).trans t2).run (by simp [machine, cfg])
  refine ⟨_, r, ?_, rfl, ?_, by omega⟩
  · have hc : (⟨machine.start, ![0, 0], ![List.replicate n true, []]⟩ : Configuration 2 3) = cfg 0 n 0 [] 0 := rfl
    rw [hc]
    have e : 1 + (n - 0) + 1 = n + 2 := by omega
    rw [e] at hr
    simpa using hr
  · rw [hf]; rfl

end NearCubicWires.PacketsGlue.CmpWord

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
noncomputable section

/-! ## Renaming the output tape of a word map -/

/-- **A word map from a machine with its output on tape `o`** (`UnaryMap.ofSwap`, word output). -/
def WordMap.ofSwap {e s : ℕ} {g : ℕ → List Bool} (M : Machine (2 + e) s) (o : Fin (2 + e)) (ho : o.val ≠ 0)
    (cost : ℕ → ℕ)
    (run : ∀ x, ∃ A' : Fin (2 + e) → List Bool,
      Step M (cost x) (fun _ => 0) (unIn (2 + e) x) (fun _ => 0) A' ∧ A' o = g x) :
    WordMap g where
  extra := e
  states := s
  machine := RecoveryFocus.machine (swapSlots e o) M
  cost := cost
  run := by
    intro x
    obtain ⟨A', hs, hA'⟩ := run x
    have d := hs.dock (swapSlots e o) (swapSlots_injective e o) (fun _ => 0) (unIn (2 + e) x)
      (fun _ => rfl)
      (by
        intro k
        unfold unIn
        by_cases hk : k.val = 0
        · rw [if_pos ((swapSlots_val_zero e o ho k).mpr hk), if_pos hk]
        · rw [if_neg (fun h => hk ((swapSlots_val_zero e o ho k).mp h)), if_neg hk])
    have e1 : swapSlots e o o = ⟨1, by omega⟩ := by
      unfold swapSlots
      by_cases h1 : o = ⟨1, by omega⟩
      · rw [if_pos h1]; exact h1
      · rw [if_neg h1, if_pos rfl]
    refine ⟨_, _, d, ?_, ?_⟩
    · rw [← e1, install_slot _ (swapSlots_injective e o)]
      exact hA'
    · rw [← e1, dockH_slot _ (swapSlots_injective e o)]

/-! ## The zero digit word -/

theorem zero_step (w : ℕ) : ∃ A' : Fin (2 + 3) → List Bool,
    Step ClockNormalize.machine (4 * w + 4) (fun _ => 0) (unIn (2 + 3) w) (fun _ => 0) A' ∧
      A' ⟨2, by omega⟩ = RepairOrdinary.frame (SignedSortKey.binary w 0) := by
  obtain ⟨r, hr, _, _, h2, _, _, hh, hs⟩ := ClockScalarFields.zero_run w
  have hin : unIn (2 + 3) w = ClockScalarFields.zeroInput w := by
    funext i; fin_cases i <;> rfl
  refine ⟨r.final.tapes, ⟨r, ?_, funext hh, rfl, by omega⟩, h2⟩
  rw [hin]
  exact hr

/-- **`frame (binary W 0)` from `1^W`.** -/
def zeroWordMap : WordMap (fun w => RepairOrdinary.frame (SignedSortKey.binary w 0)) :=
  WordMap.ofSwap (e := 3) ClockNormalize.machine ⟨2, by omega⟩ (by simp) (fun w => 4 * w + 4) zero_step

/-! ## The zero test -/

/-- **`[n = 0]` in unary** (`BitAt` at cell 0 of `1^n`, under the masked reset). -/
def isZeroMap : UnaryMap (fun n => if n = 0 then 1 else 0) where
  extra := 1
  states := 2 + 2
  machine := MaskedReset.machine (BitAt.machine 0 false) (fun _ => true)
  cost := fun _ => 2 * 1 + 2
  run := by
    intro n
    obtain ⟨H, hs⟩ := BitAt.run 0 false (List.replicate n true)
    have hs' : Step (BitAt.machine 0 false) 1 (fun _ => 0) ![List.replicate n true, []] H
        ![List.replicate n true, List.replicate (if n = 0 then 1 else 0) true] := by
      have e : (if readTapeBit (List.replicate n true) 0 = false then 1 else 0) = (if n = 0 then 1 else 0) := by
        rw [PacketsGlue.PrimeCount.read_rep]
        by_cases h : n = 0 <;> simp [h]
      rw [← e, ← heads0_2]
      exact hs
    obtain ⟨k, hm⟩ := step_mask0 hs' (fun _ => true) (by intro i _; rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]
    · rfl
    · rfl

/-! ## Two-argument word maps and `pairW` -/

/-- **A two-argument word map**: `(x, y) ↦ g x y` on tape 2 (head 0); private tapes existential. -/
structure WordMap2 (g : ℕ → ℕ → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (3 + extra) states
  cost : ℕ → ℕ → ℕ
  run : ∀ x y, ∃ (H' : Fin (3 + extra) → ℕ) (A' : Fin (3 + extra) → List Bool),
    Step machine (cost x y) (fun _ => 0) (unIn2 (3 + extra) x y) H' A' ∧
    A' ⟨2, by omega⟩ = g x y ∧ H' ⟨2, by omega⟩ = 0

/-- The composite machine. -/
def pairWMachine {a : DecompositionAlgorithm} {v1 v2 : Request → ℕ} {g : ℕ → ℕ → List Bool}
    (s1 : UnaryStage a v1) (s2 : UnaryStage a v2) (m : WordMap2 g) :=
  Composition.machine
    (Composition.machine (RecoveryFocus.machine (pA s1.extra s2.extra m.extra) s1.machine)
      (RecoveryFocus.machine (pB s1.extra s2.extra m.extra) s2.machine))
    (RecoveryFocus.machine (pM s1.extra s2.extra m.extra) m.machine)

theorem pairW_run {a : DecompositionAlgorithm} {v1 v2 : Request → ℕ} {g : ℕ → ℕ → List Bool}
    (s1 : UnaryStage a v1) (s2 : UnaryStage a v2) (m : WordMap2 g) (r : Request) :
    ∃ (H' : Fin (2 + (s1.extra + s2.extra + m.extra + 2)) → ℕ)
      (A' : Fin (2 + (s1.extra + s2.extra + m.extra + 2)) → List Bool),
      Step (pairWMachine s1 s2 m) (s1.cost r + 1 + s2.cost r + 1 + m.cost (v1 r) (v2 r)) (fun _ => 0)
        (inBank (2 + (s1.extra + s2.extra + m.extra + 2)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = g (v1 r) (v2 r) ∧ H' ⟨1, by omega⟩ = 0 := by
  set e1 := s1.extra
  set e2 := s2.extra
  set em := m.extra
  set T := 2 + (e1 + e2 + em + 2)
  set I := inBank T (Request.input a r) with hI
  obtain ⟨H1, A1, hs1, a10, h10, a11, h11⟩ := s1.run r
  have d1 := hs1.dock (pA e1 e2 em) (pA_injective _ _ _) (fun _ => 0) I (fun _ => rfl)
    (by
      intro k
      rw [hI, inBank_val, inBank_val]
      by_cases hk : k.val = 0
      · rw [if_pos (by rw [pA_val, if_pos hk]), if_pos hk]
      · rw [if_neg (pA_val_ne_zero _ _ _ k hk), if_neg hk])
  set H1' := dockH (pA e1 e2 em) (fun _ => 0) H1 with hH1'
  set A1' := install (pA e1 e2 em) I A1 with hA1'
  obtain ⟨H2, A2, hs2, a20, h20, a21, h21⟩ := s2.run r
  have d2 := hs2.dock (pB e1 e2 em) (pB_injective _ _ _) H1' A1'
    (by
      intro k
      by_cases hk : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [hk', pB_zero, hH1', dockH_slot _ (pA_injective _ _ _)]
        exact h10
      · rw [hH1', dockH_other _ _ _ _ (fun j => pB_off_pA _ _ _ k hk j)])
    (by
      intro k
      by_cases hk : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [hk', pB_zero, hA1', install_slot _ (pA_injective _ _ _), a10]
        rfl
      · rw [hA1', install_other _ _ _ _ (fun j => pB_off_pA _ _ _ k hk j), hI, inBank_val, inBank_val,
          if_neg (pB_val_ne_zero _ _ _ k hk), if_neg hk])
  set H2' := dockH (pB e1 e2 em) H1' H2 with hH2'
  set A2' := install (pB e1 e2 em) A1' A2 with hA2'
  obtain ⟨H3, A3, hm, a32, h32⟩ := m.run (v1 r) (v2 r)
  have d3 := hm.dock (pM e1 e2 em) (pM_injective _ _ _) H2' A2'
    (by
      intro k
      by_cases hk0 : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [hk', hH2', dockH_other _ _ _ _ (fun j => pM_off_pB _ _ _ _ (by simp) j), pM_zero, hH1',
          dockH_slot _ (pA_injective _ _ _)]
        exact h11
      · by_cases hk1 : k.val = 1
        · have hk' : k = ⟨1, by omega⟩ := Fin.ext hk1
          rw [hk', pM_one, hH2', dockH_slot _ (pB_injective _ _ _)]
          exact h21
        · rw [hH2', dockH_other _ _ _ _ (fun j => pM_off_pB _ _ _ k hk1 j), hH1',
            dockH_other _ _ _ _ (fun j => pM_off_pA _ _ _ k hk0 j)])
    (by
      intro k
      by_cases hk0 : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [hk', hA2', install_other _ _ _ _ (fun j => pM_off_pB _ _ _ _ (by simp) j), pM_zero, hA1',
          install_slot _ (pA_injective _ _ _), a11]
        simp [unIn2]
      · by_cases hk1 : k.val = 1
        · have hk' : k = ⟨1, by omega⟩ := Fin.ext hk1
          rw [hk', pM_one, hA2', install_slot _ (pB_injective _ _ _), a21]
          simp [unIn2]
        · rw [hA2', install_other _ _ _ _ (fun j => pM_off_pB _ _ _ k hk1 j), hA1',
            install_other _ _ _ _ (fun j => pM_off_pA _ _ _ k hk0 j), hI, inBank_val,
            if_neg (pM_ne_zero _ _ _ k)]
          simp [unIn2, hk0, hk1])
  have hall := (d1.seq d2).seq d3
  have e0 : (⟨0, by omega⟩ : Fin T) = pB e1 e2 em ⟨0, by omega⟩ := by
    apply Fin.ext; rw [pB_val]; simp
  have e1' : (⟨1, by omega⟩ : Fin T) = pM e1 e2 em ⟨2, by omega⟩ := by
    apply Fin.ext; rw [pM_val]; simp
  have n0 : ∀ k, pM e1 e2 em k ≠ ⟨0, by omega⟩ := by
    intro k h
    have hv : (pM e1 e2 em k).val = 0 := by rw [h]
    exact pM_ne_zero _ _ _ k hv
  refine ⟨_, _, hall, ?_, ?_, ?_, ?_⟩
  · rw [install_other _ _ _ _ n0, e0, hA2', install_slot _ (pB_injective _ _ _)]
    exact a20
  · rw [dockH_other _ _ _ _ n0, e0, hH2', dockH_slot _ (pB_injective _ _ _)]
    exact h20
  · rw [e1', install_slot _ (pM_injective _ _ _)]
    exact a32
  · rw [e1', dockH_slot _ (pM_injective _ _ _)]
    exact h32

/-- **Two stages, then a two-argument word map on their values.** -/
def UnaryStage.pairW {a : DecompositionAlgorithm} {v1 v2 : Request → ℕ} {g : ℕ → ℕ → List Bool}
    (s1 : UnaryStage a v1) (s2 : UnaryStage a v2) (m : WordMap2 g) (c d : ℕ)
    (hc : ∀ r, m.cost (v1 r) (v2 r) ≤ c * (r.smallSize a) ^ d) :
    WordStage a (fun r => g (v1 r) (v2 r)) where
  extra := s1.extra + s2.extra + m.extra + 2
  states := _
  machine := pairWMachine s1 s2 m
  cost := fun r => s1.cost r + 1 + s2.cost r + 1 + m.cost (v1 r) (v2 r)
  coefficient := s1.coefficient + s2.coefficient + 2 + c
  degree := s1.degree + s2.degree + d
  cost_le := by
    intro r
    set D := s1.degree + s2.degree + d
    have h1 := s1.cost_le r
    have h2 := s2.cost_le r
    have h3 := hc r
    have p1 : (r.smallSize a) ^ s1.degree ≤ (r.smallSize a) ^ D :=
      Nat.pow_le_pow_right (one_le_small a r) (by omega)
    have p2 : (r.smallSize a) ^ s2.degree ≤ (r.smallSize a) ^ D :=
      Nat.pow_le_pow_right (one_le_small a r) (by omega)
    have p3 : (r.smallSize a) ^ d ≤ (r.smallSize a) ^ D :=
      Nat.pow_le_pow_right (one_le_small a r) (by omega)
    have p0 : 1 ≤ (r.smallSize a) ^ D := Nat.one_le_pow _ _ (one_le_small a r)
    have q1 := Nat.mul_le_mul_left s1.coefficient p1
    have q2 := Nat.mul_le_mul_left s2.coefficient p2
    have q3 := Nat.mul_le_mul_left c p3
    calc s1.cost r + 1 + s2.cost r + 1 + m.cost (v1 r) (v2 r)
        ≤ s1.coefficient * (r.smallSize a) ^ D + (r.smallSize a) ^ D + s2.coefficient * (r.smallSize a) ^ D +
            (r.smallSize a) ^ D + c * (r.smallSize a) ^ D := by omega
      _ = (s1.coefficient + s2.coefficient + 2 + c) * (r.smallSize a) ^ D := by ring
  run := pairW_run s1 s2 m

/-! ## The flag word `frame (binary W b)` for `b ≤ 1` -/

def slF : Fin 3 → Fin 7 := ![1, 3, 4]
def slN : Fin 5 → Fin 7 := ![0, 3, 2, 5, 6]

theorem slF_inj : Function.Injective slF := by decide
theorem slN_inj : Function.Injective slN := by decide

def flagMachine :=
  Composition.machine (RecoveryFocus.machine slF (MaskedReset.machine FrameUnary.machine (fun _ => true)))
    (RecoveryFocus.machine slN ClockNormalize.machine)

theorem flag_step (W b : ℕ) : ∃ (H' : Fin 7 → ℕ) (A' : Fin 7 → List Bool),
    Step flagMachine (2 * (2 * b + 1) + 2 + 1 + (4 * W + 4)) (fun _ => 0) (unIn2 7 W b) H' A' ∧
      A' 2 = RepairOrdinary.frame (ClockNormalize.resize W (List.replicate b true)) ∧ H' 2 = 0 := by
  obtain ⟨H, hs⟩ := FrameUnary.run b
  have hs' : Step FrameUnary.machine (2 * b + 1) (fun _ => 0) ![List.replicate b true, []] H
      ![List.replicate b true, RepairOrdinary.frame (List.replicate b true)] := by
    rw [← heads0_2]; exact hs
  obtain ⟨k, hm⟩ := step_mask0 hs' (fun _ => true) (by intro i _; rfl)
  have hm' : Step (MaskedReset.machine FrameUnary.machine (fun _ => true)) (2 * (2 * b + 1) + 2) (fun _ => 0)
      ![List.replicate b true, [], []] (fun _ => 0)
      ![List.replicate b true, RepairOrdinary.frame (List.replicate b true), List.replicate k false] := by
    refine (hm.congr_in ?_ ?_).congr ?_ ?_
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; fin_cases i <;> rfl
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; fin_cases i <;> rfl
  have d1 := hm'.dock slF slF_inj (fun _ => 0) (unIn2 7 W b) (fun _ => rfl) (by
    intro k; fin_cases k <;> rfl)
  rw [dockH_zero] at d1
  obtain ⟨rN, hrN, hN0, hN1, hN2, hN3, hN4, hNh, hNs⟩ := ClockNormalize.normalize_run W (List.replicate b true)
  have hN : Step ClockNormalize.machine (4 * W + 4) (fun _ => 0) (ClockNormalize.input W (List.replicate b true))
      (fun _ => 0) rN.final.tapes := ⟨rN, hrN, funext hNh, rfl, by omega⟩
  set A1 := install slF (unIn2 7 W b)
    ![List.replicate b true, RepairOrdinary.frame (List.replicate b true), List.replicate k false] with hA1
  have d2 := hN.dock slN slN_inj (fun _ => 0) A1 (fun _ => rfl) (by
    intro j
    fin_cases j
    · show A1 (slN 0) = _
      rw [hA1, install_other _ _ _ _ (by decide)]; rfl
    · show A1 (slN 1) = _
      rw [show slN 1 = slF 1 from rfl, hA1, install_slot _ slF_inj]; rfl
    · show A1 (slN 2) = _
      rw [hA1, install_other _ _ _ _ (by decide)]; rfl
    · show A1 (slN 3) = _
      rw [hA1, install_other _ _ _ _ (by decide)]; rfl
    · show A1 (slN 4) = _
      rw [hA1, install_other _ _ _ _ (by decide)]; rfl)
  rw [dockH_zero] at d2
  refine ⟨_, _, d1.seq d2, ?_, ?_⟩
  · rw [show (2 : Fin 7) = slN 2 from rfl, install_slot _ slN_inj]
    exact hN2
  · rfl

/-- **`frame (resize W (1^b))` from `1^W`, `1^b`.** -/
def flagWordMap2 : WordMap2 (fun W b => RepairOrdinary.frame (ClockNormalize.resize W (List.replicate b true))) where
  extra := 4
  states := _
  machine := flagMachine
  cost := fun W b => 2 * (2 * b + 1) + 2 + 1 + (4 * W + 4)
  run := by
    intro W b
    obtain ⟨H', A', h, h2, hh2⟩ := flag_step W b
    exact ⟨H', A', h, h2, hh2⟩

/-- For `b ≤ 1 ≤ W` the flag word is `frame (binary W b)`. -/
theorem flag_word (W b : ℕ) (hb : b ≤ 1) (hW : 1 ≤ W) :
    RepairOrdinary.frame (ClockNormalize.resize W (List.replicate b true)) =
      RepairOrdinary.frame (SignedSortKey.binary W b) := by
  have hl : (List.replicate b true).length ≤ W := by simp; omega
  rw [ClockScalarFields.resize_binary W _ hl]
  congr 2
  rcases (show b = 0 ∨ b = 1 by omega) with h | h <;> subst h <;> rfl

/-! ## The row-count driver word -/

theorem cmp_step (n : ℕ) : ∃ (H' : Fin (2 + 1) → ℕ) (A' : Fin (2 + 1) → List Bool),
    Step (MaskedReset.machine CmpWord.machine (fun _ => true)) (2 * (n + 2) + 2) (fun _ => 0) (unIn (2 + 1) n) H' A' ∧
      A' ⟨1, by omega⟩ = RepairSource.VerifierDecoding.CompareMachine.word n ∧ H' ⟨1, by omega⟩ = 0 := by
  obtain ⟨H, hs⟩ := CmpWord.run n
  have hs' : Step CmpWord.machine (n + 2) (fun _ => 0) ![List.replicate n true, []] H
      ![List.replicate n true, false :: List.replicate n true] := by
    rw [← heads0_2]; exact hs
  obtain ⟨k, hm⟩ := step_mask0 hs' (fun _ => true) (by intro i _; rfl)
  refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]; fin_cases j <;> rfl
    · simp [unIn]
  · rfl
  · rfl

/-- **`CompareMachine.word n` from `1^n`.** -/
def cmpWordMap : WordMap (fun n => RepairSource.VerifierDecoding.CompareMachine.word n) where
  extra := 1
  states := 3 + 2
  machine := MaskedReset.machine CmpWord.machine (fun _ => true)
  cost := fun n => 2 * (n + 2) + 2
  run := cmp_step

end
end NearCubicWires.PacketsGlue.RequestMeta

