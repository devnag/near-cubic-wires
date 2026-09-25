import Proof.MachineModel.Runs

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsSeed
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding

/-! ## Cell words -/

/-- The second cell of each of the `n` pairs starting at pair `a`. -/
def oddCells (S : List Bool) (a n : ℕ) : List Bool :=
  (List.range n).map (fun i => readTapeBit S (2 * (a + i) + 1))

/-- The `n` pairs starting at pair `a`, verbatim. -/
def pairCells (S : List Bool) (a n : ℕ) : List Bool :=
  (List.range n).flatMap (fun i => [readTapeBit S (2 * (a + i)), readTapeBit S (2 * (a + i) + 1)])

theorem oddCells_succ (S : List Bool) (a n : ℕ) :
    oddCells S a (n + 1) = oddCells S a n ++ [readTapeBit S (2 * (a + n) + 1)] := by
  simp [oddCells, List.range_succ]

theorem pairCells_succ (S : List Bool) (a n : ℕ) :
    pairCells S a (n + 1) =
      pairCells S a n ++ [readTapeBit S (2 * (a + n)), readTapeBit S (2 * (a + n) + 1)] := by
  simp [pairCells, List.range_succ, List.flatMap_append]

@[simp] theorem oddCells_length (S : List Bool) (a n : ℕ) : (oddCells S a n).length = n := by
  simp [oddCells]

@[simp] theorem pairCells_length (S : List Bool) (a n : ℕ) : (pairCells S a n).length = 2 * n := by
  induction n with
  | zero => simp [pairCells]
  | succ n ih => rw [pairCells_succ, List.length_append, ih]; simp; omega

/-! ## The machine -/

/-- States: 0 label check, 1 label copy, 2 `y` check, 3 `y` copy, 4 `x` check, 5 `x` copy, 6 halt. -/
def machine : Machine 6 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 6
  rule := fun q b =>
    if q.val = 0 then
      if b 1 then some ⟨1, fun _ => none, fun i => if i.val = 0 then .right else .stay⟩
      else some ⟨2, fun _ => none, fun i => if i.val = 2 then .right else .stay⟩
    else if q.val = 1 then
      some ⟨0, fun i => if i.val = 3 then some (b 0) else none,
        fun i => if i.val = 0 ∨ i.val = 1 ∨ i.val = 3 then .right else .stay⟩
    else if q.val = 2 then
      if b 2 then some ⟨3, fun i => if i.val = 4 then some (b 0) else none,
        fun i => if i.val = 0 ∨ i.val = 4 then .right else .stay⟩
      else some ⟨4, fun i => if i.val = 4 then some false else none,
        fun i => if i.val = 2 then .left else .stay⟩
    else if q.val = 3 then
      some ⟨2, fun i => if i.val = 4 then some (b 0) else none,
        fun i => if i.val = 0 ∨ i.val = 2 ∨ i.val = 4 then .right else .stay⟩
    else if q.val = 4 then
      if b 2 then some ⟨5, fun i => if i.val = 5 then some (b 0) else none,
        fun i => if i.val = 0 ∨ i.val = 5 then .right else .stay⟩
      else some ⟨6, fun i => if i.val = 5 then some false else none, fun _ => .stay⟩
    else if q.val = 5 then
      some ⟨4, fun i => if i.val = 5 then some (b 0) else none,
        fun i => if i.val = 0 ∨ i.val = 5 then .right else if i.val = 2 then .left else .stay⟩
    else none

section Run
variable (S : List Bool) (L s : ℕ)

/-- A configuration: the three inputs fixed, heads and outputs explicit. -/
def cfg (q : Fin 7) (h0 h1 h2 h3 h4 h5 : ℕ) (U Y X : List Bool) : Configuration 6 7 :=
  ⟨q, ![h0, h1, h2, h3, h4, h5], ![S, List.replicate L true, CompareMachine.word s, U, Y, X]⟩

theorem read_rep_lt (j : ℕ) (hj : j < L) : readTapeBit (List.replicate L true) j = true := by
  simp [readTapeBit, List.getD, hj]

theorem read_rep_ge : readTapeBit (List.replicate L true) L = false := by
  simp [readTapeBit, List.getD]

theorem step_label (j : ℕ) (hj : j < L) (U : List Bool) :
    step machine (cfg S L s 0 (2 * j) j 0 j 0 0 U [] []) =
      some (cfg S L s 1 (2 * j + 1) j 0 j 0 0 U [] []) := by
  have hr := read_rep_lt L j hj
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem step_labelCopy (j : ℕ) :
    step machine (cfg S L s 1 (2 * j + 1) j 0 j 0 0 (oddCells S 0 j) [] []) =
      some (cfg S L s 0 (2 * (j + 1)) (j + 1) 0 (j + 1) 0 0 (oddCells S 0 (j + 1)) [] []) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, HeadMove.apply]
    omega
  · funext i; fin_cases i <;> simp [applyAction]
    rw [oddCells_succ]
    have hl : (oddCells S 0 j).length = j := oddCells_length S 0 j
    have hw := Streaming.write_append (oddCells S 0 j) (readTapeBit S (2 * j + 1))
    rw [hl] at hw
    rw [hw]
    simp

theorem step_labelEnd (U : List Bool) :
    step machine (cfg S L s 0 (2 * L) L 0 L 0 0 U [] []) =
      some (cfg S L s 2 (2 * L) L 1 L 0 0 U [] []) := by
  have hr := read_rep_ge L
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem step_y (k : ℕ) (hk : k < s) (U : List Bool) :
    step machine (cfg S L s 2 (2 * (L + k)) L (k + 1) L (2 * k) 0 U (pairCells S L k) []) =
      some (cfg S L s 3 (2 * (L + k) + 1) L (k + 1) L (2 * k + 1) 0 U
        (pairCells S L k ++ [readTapeBit S (2 * (L + k))]) []) := by
  have hr : readTapeBit (CompareMachine.word s) (k + 1) = true := by
    rw [CompareMachine.read_mark]; simp [hk]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]
    have hl : (pairCells S L k).length = 2 * k := pairCells_length S L k
    have hw := Streaming.write_append (pairCells S L k) (readTapeBit S (2 * (L + k)))
    rw [hl] at hw
    exact hw

theorem step_yCopy (k : ℕ) (U : List Bool) :
    step machine (cfg S L s 3 (2 * (L + k) + 1) L (k + 1) L (2 * k + 1) 0 U
        (pairCells S L k ++ [readTapeBit S (2 * (L + k))]) []) =
      some (cfg S L s 2 (2 * (L + (k + 1))) L (k + 1 + 1) L (2 * (k + 1)) 0 U (pairCells S L (k + 1)) []) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, HeadMove.apply]
    all_goals omega
  · funext i; fin_cases i <;> simp [applyAction]
    rw [pairCells_succ]
    have hl : (pairCells S L k ++ [readTapeBit S (2 * (L + k))]).length = 2 * k + 1 := by simp
    have hw := Streaming.write_append (pairCells S L k ++ [readTapeBit S (2 * (L + k))])
      (readTapeBit S (2 * (L + k) + 1))
    rw [hl] at hw
    rw [hw]
    simp

theorem step_yEnd (U : List Bool) :
    step machine (cfg S L s 2 (2 * (L + s)) L (s + 1) L (2 * s) 0 U (pairCells S L s) []) =
      some (cfg S L s 4 (2 * (L + s)) L s L (2 * s) 0 U (pairCells S L s ++ [false]) []) := by
  have hr : readTapeBit (CompareMachine.word s) (s + 1) = false := by
    rw [CompareMachine.read_mark]; simp
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]
    have hl : (pairCells S L s).length = 2 * s := pairCells_length S L s
    have hw := Streaming.write_append (pairCells S L s) false
    rw [hl] at hw
    exact hw

theorem step_x (k m : ℕ) (hkm : k + (m + 1) = s) (U Y : List Bool) :
    step machine (cfg S L s 4 (2 * (L + s + k)) L (m + 1) L (2 * s) (2 * k) U Y (pairCells S (L + s) k)) =
      some (cfg S L s 5 (2 * (L + s + k) + 1) L (m + 1) L (2 * s) (2 * k + 1) U Y
        (pairCells S (L + s) k ++ [readTapeBit S (2 * (L + s + k))])) := by
  have hr : readTapeBit (CompareMachine.word s) (m + 1) = true := by
    rw [CompareMachine.read_mark]; simp; omega
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]
    have hl : (pairCells S (L + s) k).length = 2 * k := pairCells_length S (L + s) k
    have hw := Streaming.write_append (pairCells S (L + s) k) (readTapeBit S (2 * (L + s + k)))
    rw [hl] at hw
    exact hw

theorem step_xCopy (k m : ℕ) (U Y : List Bool) :
    step machine (cfg S L s 5 (2 * (L + s + k) + 1) L (m + 1) L (2 * s) (2 * k + 1) U Y
        (pairCells S (L + s) k ++ [readTapeBit S (2 * (L + s + k))])) =
      some (cfg S L s 4 (2 * (L + s + (k + 1))) L m L (2 * s) (2 * (k + 1)) U Y
        (pairCells S (L + s) (k + 1))) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, HeadMove.apply]
    all_goals omega
  · funext i; fin_cases i <;> simp [applyAction]
    rw [pairCells_succ]
    have hl : (pairCells S (L + s) k ++ [readTapeBit S (2 * (L + s + k))]).length = 2 * k + 1 := by simp
    have hw := Streaming.write_append (pairCells S (L + s) k ++ [readTapeBit S (2 * (L + s + k))])
      (readTapeBit S (2 * (L + s + k) + 1))
    rw [hl] at hw
    rw [hw]
    simp

theorem step_xEnd (U Y : List Bool) :
    step machine (cfg S L s 4 (2 * (L + s + s)) L 0 L (2 * s) (2 * s) U Y (pairCells S (L + s) s)) =
      some (cfg S L s 6 (2 * (L + s + s)) L 0 L (2 * s) (2 * s) U Y (pairCells S (L + s) s ++ [false])) := by
  have hr : readTapeBit (CompareMachine.word s) 0 = false := CompareMachine.read_zero s
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]
    have hl : (pairCells S (L + s) s).length = 2 * s := pairCells_length S (L + s) s
    have hw := Streaming.write_append (pairCells S (L + s) s) false
    rw [hl] at hw
    exact hw

/-! ## The three loops -/

theorem labels_loop (m j : ℕ) (h : j + m = L) :
    Timed machine (2 * m + 1) (cfg S L s 0 (2 * j) j 0 j 0 0 (oddCells S 0 j) [] [])
      (cfg S L s 2 (2 * L) L 1 L 0 0 (oddCells S 0 L) [] []) := by
  induction m generalizing j with
  | zero =>
    have hj : j = L := by omega
    subst hj
    exact Timed.single (by rfl) (step_labelEnd S j s _)
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [e]
    exact Timed.step (by rfl) (step_label S L s j (by omega) _)
      (Timed.step (by rfl) (step_labelCopy S L s j) (ih (j + 1) (by omega)))

theorem y_loop (m k : ℕ) (h : k + m = s) (U : List Bool) :
    Timed machine (2 * m + 1) (cfg S L s 2 (2 * (L + k)) L (k + 1) L (2 * k) 0 U (pairCells S L k) [])
      (cfg S L s 4 (2 * (L + s)) L s L (2 * s) 0 U (pairCells S L s ++ [false]) []) := by
  induction m generalizing k with
  | zero =>
    have hk : k = s := by omega
    subst hk
    exact Timed.single (by rfl) (step_yEnd S L k U)
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [e]
    exact Timed.step (by rfl) (step_y S L s k (by omega) U)
      (Timed.step (by rfl) (step_yCopy S L s k U) (ih (k + 1) (by omega)))

theorem x_loop (m k : ℕ) (h : k + m = s) (U Y : List Bool) :
    Timed machine (2 * m + 1)
      (cfg S L s 4 (2 * (L + s + k)) L m L (2 * s) (2 * k) U Y (pairCells S (L + s) k))
      (cfg S L s 6 (2 * (L + s + s)) L 0 L (2 * s) (2 * s) U Y (pairCells S (L + s) s ++ [false])) := by
  induction m generalizing k with
  | zero =>
    have hk : k = s := by omega
    subst hk
    exact Timed.single (by rfl) (step_xEnd S L k U Y)
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [e]
    exact Timed.step (by rfl) (step_x S L s k m h U Y)
      (Timed.step (by rfl) (step_xCopy S L s k m U Y) (ih (k + 1) (by omega)))

/-- The whole split, as one timed run. -/
theorem split_timed :
    Timed machine (2 * L + 4 * s + 3) (cfg S L s 0 0 0 0 0 0 0 [] [] [])
      (cfg S L s 6 (2 * (L + s + s)) L 0 L (2 * s) (2 * s) (oddCells S 0 L) (pairCells S L s ++ [false])
        (pairCells S (L + s) s ++ [false])) := by
  have h1 := labels_loop S L s L 0 (by omega)
  have h2 := y_loop S L s s 0 (by omega) (oddCells S 0 L)
  have h3 := x_loop S L s s 0 (by omega) (oddCells S 0 L) (pairCells S L s ++ [false])
  have e : 2 * L + 4 * s + 3 = 2 * L + 1 + (2 * s + 1) + (2 * s + 1) := by ring
  rw [e]
  exact (h1.trans h2).trans h3

/-- **The split, as a `Step`** from the ready bank (all heads `0`). -/
theorem split_run :
    Step machine (2 * L + 4 * s + 3) (fun _ => 0)
      ![S, List.replicate L true, CompareMachine.word s, [], [], []]
      ![2 * (L + s + s), L, 0, L, 2 * s, 2 * s]
      ![S, List.replicate L true, CompareMachine.word s, oddCells S 0 L, pairCells S L s ++ [false],
        pairCells S (L + s) s ++ [false]] := by
  obtain ⟨r, hr, hf, _⟩ := (split_timed S L s).run (by rfl)
  have hc : cfg S L s 0 0 0 0 0 0 0 [] [] [] =
      (⟨machine.start, fun _ => 0, ![S, List.replicate L true, CompareMachine.word s, [], [], []]⟩ :
        Configuration 6 7) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hc] at hr
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

end Run

end NearCubicWires.PacketsSeed
