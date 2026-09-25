import Proof.Packets.PacketsSetupDriver

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsGlue.Nest
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

theorem hd_val : ∀ (k : ℕ) (out : List Bool) (j : Fin (1 + k)),
    hd k out j = if j.val = 0 then out.length + 1 else 0 := by
  intro k
  induction k with
  | zero => intro out j; have hj : j.val = 0 := by omega
            rw [if_pos hj]; have : j = 0 := Fin.ext hj; subst this; rfl
  | succ k ih =>
    intro out j
    simp only [hd]
    rw [ac1]
    by_cases h : j.val < 1 + k
    · rw [dif_pos h, ih]
    · rw [dif_neg h, if_neg (by omega)]

theorem tp_val (m P : ℕ) : ∀ (k : ℕ) (out : List Bool) (j : Fin (1 + k)),
    tp m P k out j = if j.val = 0 then false :: out ++ List.replicate (P - out.length) false
      else RepairSource.VerifierDecoding.CompareMachine.word m := by
  intro k
  induction k with
  | zero => intro out j; have hj : j.val = 0 := by omega
            rw [if_pos hj]; have : j = 0 := Fin.ext hj; subst this; rfl
  | succ k ih =>
    intro out j
    simp only [tp]
    rw [ac1]
    by_cases h : j.val < 1 + k
    · rw [dif_pos h, ih]
    · rw [dif_neg h, if_neg (by omega)]

end NearCubicWires.PacketsGlue.Nest

namespace NearCubicWires.PacketsGlue.DriverPhase
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue.CeilSqrt (sentC)
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.PacketsGlue.RequestMeta (dockH_zero)

/-! ## Slots -/

def stSlots (k : ℕ) : Fin (2 + k) → Fin (4 + k) := fun j => ⟨j.val + 2, by omega⟩
def neSlots (k : ℕ) : Fin (1 + (k + 1)) → Fin (4 + k) :=
  fun j => if j.val = 0 then ⟨0, by omega⟩ else ⟨j.val + 2, by omega⟩
def drSlots (k : ℕ) : Fin 2 → Fin (4 + k) := fun j => ⟨j.val, by omega⟩
def moveL (k : ℕ) : Fin (4 + k) → HeadMove := fun i => if i.val = 0 then .right else .stay

theorem st_inj (k : ℕ) : Function.Injective (stSlots k) := by
  intro x y h; have := congrArg Fin.val h; simp [stSlots] at this; exact Fin.ext this

theorem ne_val (k : ℕ) (j : Fin (1 + (k + 1))) : (neSlots k j).val = if j.val = 0 then 0 else j.val + 2 := by
  unfold neSlots; split_ifs <;> rfl

theorem ne_inj (k : ℕ) : Function.Injective (neSlots k) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [ne_val, ne_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem dr_inj (k : ℕ) : Function.Injective (drSlots k) := by
  intro x y h; have := congrArg Fin.val h; simp [drSlots] at this; exact Fin.ext this

theorem inst_st {k : ℕ} (B : Fin (4 + k) → List Bool) (T : Fin (2 + k) → List Bool) (i : Fin (4 + k)) :
    install (stSlots k) B T i = if h : 2 ≤ i.val then T ⟨i.val - 2, by omega⟩ else B i := by
  by_cases h : 2 ≤ i.val
  · rw [dif_pos h]
    have e : stSlots k ⟨i.val - 2, by omega⟩ = i := Fin.ext (by simp [stSlots]; omega)
    have := install_slot (stSlots k) (st_inj k) B T ⟨i.val - 2, by omega⟩
    rw [e] at this
    exact this
  · rw [dif_neg h, install_other]
    intro j hj; have := congrArg Fin.val hj; simp [stSlots] at this; omega

theorem ne_at (k : ℕ) (i : Fin (4 + k)) (h : 3 ≤ i.val) : neSlots k ⟨i.val - 2, by omega⟩ = i := by
  apply Fin.ext
  rw [ne_val]
  have hne : ¬ ((⟨i.val - 2, by omega⟩ : Fin (1 + (k + 1))).val = 0) := by simp; omega
  rw [if_neg hne]
  simp
  omega

theorem ne_at0 (k : ℕ) (i : Fin (4 + k)) (h0 : i.val = 0) : neSlots k ⟨0, by omega⟩ = i := by
  apply Fin.ext
  rw [ne_val]
  simp [h0]

theorem inst_ne {k : ℕ} (B : Fin (4 + k) → List Bool) (T : Fin (1 + (k + 1)) → List Bool) (i : Fin (4 + k)) :
    install (neSlots k) B T i =
      if h0 : i.val = 0 then T ⟨0, by omega⟩ else if h : 3 ≤ i.val then T ⟨i.val - 2, by omega⟩ else B i := by
  by_cases h0 : i.val = 0
  · rw [dif_pos h0]
    have := install_slot (neSlots k) (ne_inj k) B T ⟨0, by omega⟩
    rw [ne_at0 k i h0] at this
    exact this
  · rw [dif_neg h0]
    by_cases h : 3 ≤ i.val
    · rw [dif_pos h]
      have := install_slot (neSlots k) (ne_inj k) B T ⟨i.val - 2, by omega⟩
      rw [ne_at k i h] at this
      exact this
    · rw [dif_neg h, install_other]
      intro j hj; have := congrArg Fin.val hj; rw [ne_val] at this; split_ifs at this <;> omega

theorem inst_dr {k : ℕ} (B : Fin (4 + k) → List Bool) (T : Fin 2 → List Bool) (i : Fin (4 + k)) :
    install (drSlots k) B T i = if h : i.val < 2 then T ⟨i.val, h⟩ else B i := by
  by_cases h : i.val < 2
  · rw [dif_pos h]
    have e : drSlots k ⟨i.val, h⟩ = i := Fin.ext (by simp [drSlots])
    have := install_slot (drSlots k) (dr_inj k) B T ⟨i.val, h⟩
    rw [e] at this
    exact this
  · rw [dif_neg h, install_other]
    intro j hj; have := congrArg Fin.val hj; simp [drSlots] at this; omega

theorem dock_ne {k : ℕ} (H : Fin (4 + k) → ℕ) (T : Fin (1 + (k + 1)) → ℕ) (i : Fin (4 + k)) :
    dockH (neSlots k) H T i =
      if h0 : i.val = 0 then T ⟨0, by omega⟩ else if h : 3 ≤ i.val then T ⟨i.val - 2, by omega⟩ else H i := by
  by_cases h0 : i.val = 0
  · rw [dif_pos h0]
    have := dockH_slot (neSlots k) (ne_inj k) H T ⟨0, by omega⟩
    rw [ne_at0 k i h0] at this
    exact this
  · rw [dif_neg h0]
    by_cases h : 3 ≤ i.val
    · rw [dif_pos h]
      have := dockH_slot (neSlots k) (ne_inj k) H T ⟨i.val - 2, by omega⟩
      rw [ne_at k i h] at this
      exact this
    · rw [dif_neg h, dockH_other]
      intro j hj; have := congrArg Fin.val hj; rw [ne_val] at this; split_ifs at this <;> omega

theorem dock_dr {k : ℕ} (H : Fin (4 + k) → ℕ) (T : Fin 2 → ℕ) (i : Fin (4 + k)) :
    dockH (drSlots k) H T i = if h : i.val < 2 then T ⟨i.val, h⟩ else H i := by
  by_cases h : i.val < 2
  · rw [dif_pos h]
    have e : drSlots k ⟨i.val, h⟩ = i := Fin.ext (by simp [drSlots])
    have := dockH_slot (drSlots k) (dr_inj k) H T ⟨i.val, h⟩
    rw [e] at this
    exact this
  · rw [dif_neg h, dockH_other]
    intro j hj; have := congrArg Fin.val hj; simp [drSlots] at this; omega

/-! ## The machine and its banks -/

noncomputable def machine (c k : ℕ) :=
  Composition.machine (RecoveryFocus.machine (stSlots k) (Stamp.machine k))
    (Composition.machine (DecompositionCountPosition.move (moveL k))
      (Composition.machine (RecoveryFocus.machine (neSlots k) (Nest.lvl c (k + 1)).2)
        (RecoveryFocus.machine (drSlots k) Drain.machine)))

def cost (c k m : ℕ) : ℕ :=
  (2 * m + 3) + 1 + (1 + 1 + (Nest.cost c m (k + 1) + 1 + (3 * (c * m ^ (k + 1)) + 4)))

/-- Entry: the padded log, an empty driver, the source `1^m`, empty counters. -/
def entryA (k m R : ℕ) : Fin (4 + k) → List Bool := fun i =>
  if i.val = 0 then List.replicate (R + 1) false else if i.val = 2 then List.replicate m true else []

/-- Exit: the scrub log and driver, the source, the counters `word m`. -/
def exitA (k m R : ℕ) : Fin (4 + k) → List Bool := fun i =>
  if i.val = 0 then List.replicate (R + 1) false else if i.val = 1 then List.replicate R true
  else if i.val = 2 then List.replicate m true else CompareMachine.word m

def midA (k m _R : ℕ) (L : List Bool) : Fin (4 + k) → List Bool := fun i =>
  if i.val = 0 then L else if i.val = 1 then [] else if i.val = 2 then List.replicate m true
  else CompareMachine.word m

/-- **The driver phase.** -/
theorem run (c k m : ℕ) :
    Step (machine c k) (cost c k m) (fun _ => 0) (entryA k m (c * m ^ (k + 1))) (fun _ => 0)
      (exitA k m (c * m ^ (k + 1))) := by
  set R := c * m ^ (k + 1) with hR
  -- the stamp
  have s1 := (Stamp.run k m).dock (stSlots k) (st_inj k) (fun _ => 0) (entryA k m R) (fun _ => rfl)
    (by
      intro j
      simp only [entryA, stSlots, Fin.val_mk]
      split_ifs <;> first | rfl | omega | contradiction)
  rw [dockH_zero] at s1
  have e1 : install (stSlots k) (entryA k m R)
      (fun i => if i.val = 0 then List.replicate m true else CompareMachine.word m) =
      midA k m R (List.replicate (R + 1) false) := by
    funext i
    rw [inst_st]
    simp only [midA, entryA, Fin.val_mk]
    split_ifs <;> first | rfl | omega | contradiction
  rw [e1] at s1
  -- the log head to 1
  have s2 := Nest.move_step (moveL k) (fun _ => 0) (midA k m R (List.replicate (R + 1) false))
  have e2 : (fun i => (moveL k i).apply ((fun _ => 0) i)) = fun i : Fin (4 + k) => if i.val = 0 then 1 else 0 := by
    funext i; unfold moveL; split_ifs <;> rfl
  rw [e2] at s2
  -- the nest
  have s3 := (Nest.run c m R (k + 1) []).dock (neSlots k) (ne_inj k) (fun i : Fin (4 + k) => if i.val = 0 then 1 else 0)
    (midA k m R (List.replicate (R + 1) false))
    (by
      intro j
      rw [Nest.hd_val, ne_val]
      split_ifs <;> first | rfl | omega)
    (by
      intro j
      rw [Nest.tp_val]
      simp only [midA, ne_val]
      split_ifs <;> first | rfl | omega | contradiction | simp [List.replicate_succ])
  have e3h : dockH (neSlots k) (fun i : Fin (4 + k) => if i.val = 0 then 1 else 0)
      (Nest.hd (k + 1) ([] ++ List.replicate (c * m ^ (k + 1)) true)) =
      fun i : Fin (4 + k) => if i.val = 0 then R + 1 else 0 := by
    funext i
    rw [dock_ne]
    simp only [Nest.hd_val]
    split_ifs <;> first | rfl | omega | contradiction | simp [hR]
  have e3a : install (neSlots k) (midA k m R (List.replicate (R + 1) false))
      (Nest.tp m R (k + 1) ([] ++ List.replicate (c * m ^ (k + 1)) true)) = midA k m R (sentC R) := by
    funext i
    rw [inst_ne]
    simp only [midA, Nest.tp_val]
    split_ifs <;> first | rfl | omega | contradiction | simp [sentC, hR]
  rw [e3h, e3a] at s3
  -- the drain
  have s4 := (Drain.run R).dock (drSlots k) (dr_inj k) (fun i : Fin (4 + k) => if i.val = 0 then R + 1 else 0)
    (midA k m R (sentC R))
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  have e4h : dockH (drSlots k) (fun i : Fin (4 + k) => if i.val = 0 then R + 1 else 0) ![0, 0] = fun _ => 0 := by
    funext i
    rw [dock_dr]
    split_ifs with h h'
    · have : i.val = 0 ∨ i.val = 1 := by omega
      rcases this with e | e <;> simp [e]
    · omega
    · rfl
  have e4a : install (drSlots k) (midA k m R (sentC R)) ![List.replicate (R + 1) false, List.replicate R true] =
      exitA k m R := by
    funext i
    rw [inst_dr]
    simp only [exitA, midA]
    split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | omega | skip
    all_goals first
      | (have e : i.val = 0 := by omega
         simp [e])
      | (have e : i.val = 1 := by omega
         simp [e])
  rw [e4h, e4a] at s4
  exact s1.seq (s2.seq (s3.seq s4))

end NearCubicWires.PacketsGlue.DriverPhase

