import Proof.Packets.PacketsCombineTabLoop

/-! # P2 (iii) table writer, part 6: the static-tape generators

Consumer: the table writer's loop (`PacketsCombineTabLoop.loop_run`), whose entry needs the odometer's
static tapes `[true]`, `Tt (pop+1) (replicate D 0)` (code `0`), `Bt (pop+1) D`, the register `word (p-1)` and
the loop driver `CompareMachine.word N`, EXACTLY. Every input is a tape that only has to READ as a unary word
(`ReadsWord`: `UnaryTemplate.tape X` and `CompareMachine.word X` both do). Paper: A.13.7
(`paper.tex:3113-3142`), internal preprocessing charged in `T_prep` (`paper.tex:1197-1200`); budget class
source-polynomial (`genCost`, `ucopyCost` are linear/quadratic in `pop, D, X`).

* `genTB : Machine 5 9` (tapes `pop`, `D`, `L`, `T`, `B`; the last three blank): writes `L = [true]`,
  `T = Tt (pop+1) (replicate D 0)`, `B = Bt (pop+1) D`, every head back at `0`.
* `ucopy skip park : Machine 2 7` (tapes: input, blank output): writes `CompareMachine.word X` where the input
  reads as `word (X + [skip])`; input head back at `0`, output head at `0` (or `1` if `park`).
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

/-! ## The static tapes as flattened blocks -/

/-- The block of digit `0`: `true` then `pop` clear cells. -/
def blk (pop : ℕ) : List Bool := true :: List.replicate pop false

/-- `j` blocks of digit `0`. -/
def blks (pop j : ℕ) : List Bool := (List.replicate j (blk pop)).flatten

theorem blks_succ (pop j : ℕ) : blks pop (j + 1) = blks pop j ++ blk pop := by
  unfold blks
  rw [List.replicate_succ', List.flatten_append, List.flatten_singleton]

theorem blks_length (pop j : ℕ) : (blks pop j).length = j * (pop + 1) := by
  induction j with
  | zero => simp [blks]
  | succ j ih => rw [blks_succ, List.length_append, ih, blk, List.length_cons, List.length_replicate, Nat.succ_mul]

theorem oneHot_zero (pop : ℕ) : oneHot (pop + 1) 0 = blk pop := by
  unfold oneHot blk
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Fin.val_succ, decide_true, List.cons.injEq, true_and]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_replicate]
  simp only [decide_eq_false_iff_not]
  omega

theorem Tt_zeros (pop D : ℕ) : Tt (pop + 1) (List.replicate D 0) = false :: blks pop D := by
  unfold Tt blocksOf blks
  rw [List.map_replicate, oneHot_zero]

theorem cons_true_flatten (X : List Bool) : ∀ D, true :: (List.replicate D (X ++ [true])).flatten =
    (List.replicate D (true :: X)).flatten ++ [true] := by
  intro D
  induction D with
  | zero => rfl
  | succ D ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.append_assoc, List.cons_append, List.nil_append]
    rw [ih]

theorem Bt_zeros (pop D : ℕ) : Bt (pop + 1) D = blks pop D ++ [true, true] := by
  unfold Bt bm blks blk
  rw [show pop + 1 - 1 = pop by omega, ← List.cons_append, cons_true_flatten, List.append_assoc]
  rfl

/-! ## `genTB` -/

def genTB : Machine 5 9 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 8
  rule := fun q sc =>
    if q.val = 0 then some ⟨1, ![none, none, some true, some false, none], ![.stay, .right, .right, .right, .stay]⟩
    else if q.val = 1 then some (if sc 1 then ⟨2, ![none, none, none, some true, some true],
        ![.right, .stay, .right, .right, .right]⟩
      else ⟨4, ![none, none, none, none, some true], ![.stay, .stay, .stay, .stay, .right]⟩)
    else if q.val = 2 then some (if sc 0 then ⟨2, ![none, none, none, some false, some false],
        ![.right, .stay, .right, .right, .right]⟩
      else ⟨3, ![none, none, none, none, none], ![.left, .stay, .stay, .stay, .stay]⟩)
    else if q.val = 3 then some (if sc 0 then ⟨3, ![none, none, none, none, none], ![.left, .stay, .stay, .stay, .stay]⟩
      else ⟨1, ![none, none, none, none, none], ![.stay, .right, .stay, .stay, .stay]⟩)
    else if q.val = 4 then some ⟨5, ![none, none, none, none, some true], ![.stay, .stay, .stay, .stay, .right]⟩
    else if q.val = 5 then some ⟨6, ![none, none, none, none, none], ![.stay, .left, .stay, .stay, .stay]⟩
    else if q.val = 6 then some (if sc 1 then ⟨6, ![none, none, none, none, none], ![.stay, .left, .stay, .stay, .stay]⟩
      else ⟨7, ![none, none, none, none, none], ![.stay, .stay, .stay, .stay, .stay]⟩)
    else if q.val = 7 then some (if sc 2 then ⟨8, ![none, none, none, none, none], ![.stay, .stay, .stay, .stay, .left]⟩
      else ⟨7, ![none, none, none, none, none], ![.stay, .stay, .left, .left, .left]⟩)
    else none

/-- `genTB`'s configuration after its first step (`L = [true]`). -/
def gc (P Dw : List Bool) (q : Fin 9) (a b c d : ℕ) (T B : List Bool) : Configuration 5 9 :=
  ⟨q, ![a, b, c, c, d], ![P, Dw, [true], T, B]⟩

section GenTrans
variable (P Dw : List Bool)

theorem g0 : LocalBitMultitape.step genTB ⟨0, fun _ => 0, ![P, Dw, [], [], []]⟩ =
    some (gc P Dw 1 0 1 1 0 [false] []) := by
  simp [LocalBitMultitape.step, genTB, gc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction] <;> rfl

theorem g1t (a b : ℕ) (T B : List Bool) (h : readTapeBit Dw b = true) :
    LocalBitMultitape.step genTB (gc P Dw 1 a b T.length B.length T B) =
      some (gc P Dw 2 (a + 1) b (T.length + 1) (B.length + 1) (T ++ [true]) (B ++ [true])) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, Streaming.write_append]

theorem g1f (a b c : ℕ) (T B : List Bool) (h : readTapeBit Dw b = false) :
    LocalBitMultitape.step genTB (gc P Dw 1 a b c B.length T B) =
      some (gc P Dw 4 a b c (B.length + 1) T (B ++ [true])) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, Streaming.write_append]

theorem g2t (a b : ℕ) (T B : List Bool) (h : readTapeBit P a = true) :
    LocalBitMultitape.step genTB (gc P Dw 2 a b T.length B.length T B) =
      some (gc P Dw 2 (a + 1) b (T.length + 1) (B.length + 1) (T ++ [false]) (B ++ [false])) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, Streaming.write_append]

theorem g2f (a b c d : ℕ) (T B : List Bool) (h : readTapeBit P a = false) :
    LocalBitMultitape.step genTB (gc P Dw 2 a b c d T B) = some (gc P Dw 3 (a - 1) b c d T B) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem g3t (a b c d : ℕ) (T B : List Bool) (h : readTapeBit P a = true) :
    LocalBitMultitape.step genTB (gc P Dw 3 a b c d T B) = some (gc P Dw 3 (a - 1) b c d T B) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem g3f (a b c d : ℕ) (T B : List Bool) (h : readTapeBit P a = false) :
    LocalBitMultitape.step genTB (gc P Dw 3 a b c d T B) = some (gc P Dw 1 a (b + 1) c d T B) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem g4 (a b c : ℕ) (T B : List Bool) :
    LocalBitMultitape.step genTB (gc P Dw 4 a b c B.length T B) =
      some (gc P Dw 5 a b c (B.length + 1) T (B ++ [true])) := by
  simp [LocalBitMultitape.step, genTB, gc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, Streaming.write_append]

theorem g5 (a b c d : ℕ) (T B : List Bool) :
    LocalBitMultitape.step genTB (gc P Dw 5 a b c d T B) = some (gc P Dw 6 a (b - 1) c d T B) := by
  simp [LocalBitMultitape.step, genTB, gc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem g6t (a b c d : ℕ) (T B : List Bool) (h : readTapeBit Dw b = true) :
    LocalBitMultitape.step genTB (gc P Dw 6 a b c d T B) = some (gc P Dw 6 a (b - 1) c d T B) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem g6f (a b c d : ℕ) (T B : List Bool) (h : readTapeBit Dw b = false) :
    LocalBitMultitape.step genTB (gc P Dw 6 a b c d T B) = some (gc P Dw 7 a b c d T B) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem g7f (a b c d : ℕ) (T B : List Bool) (h : readTapeBit [true] c = false) :
    LocalBitMultitape.step genTB (gc P Dw 7 a b c d T B) = some (gc P Dw 7 a b (c - 1) (d - 1) T B) := by
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem g7t (a b d : ℕ) (T B : List Bool) :
    LocalBitMultitape.step genTB (gc P Dw 7 a b 0 d T B) = some (gc P Dw 8 a b 0 (d - 1) T B) := by
  have h : readTapeBit [true] 0 = true := rfl
  simp [LocalBitMultitape.step, genTB, gc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

end GenTrans

/-! ## `genTB`'s walks -/

section GenWalks
variable (pop D : ℕ) (P Dw : List Bool) (hP : ReadsWord P pop) (hDw : ReadsWord Dw D)

include hP in
theorem inner_walk (b : ℕ) (T B : List Bool) :
    ∀ v, v ≤ pop → TimedLe genTB v (gc P Dw 2 1 b T.length B.length T B)
      (gc P Dw 2 (1 + v) b (T.length + v) (B.length + v) (T ++ List.replicate v false) (B ++ List.replicate v false)) := by
  intro v
  induction v with
  | zero =>
    intro _
    simp only [Nat.add_zero, List.replicate_zero, List.append_nil]
    exact TimedLe.refl _ _
  | succ v ih =>
    intro hv
    have s := g2t P Dw (1 + v) b (T ++ List.replicate v false) (B ++ List.replicate v false)
      (hP.pos (1 + v) (by omega) (by omega))
    simp only [List.length_append, List.length_replicate, List.append_assoc, ← List.replicate_succ'] at s
    rw [show 1 + v + 1 = 1 + (v + 1) by omega, show T.length + v + 1 = T.length + (v + 1) by omega,
      show B.length + v + 1 = B.length + (v + 1) by omega] at s
    exact (ih (by omega)).trans (TimedLe.single (by rfl) s)

include hP in
theorem pop_rewind (b c d : ℕ) (T B : List Bool) :
    ∀ k, k ≤ pop → TimedLe genTB k (gc P Dw 3 k b c d T B) (gc P Dw 3 0 b c d T B) := by
  intro k
  induction k with
  | zero => intro _; exact TimedLe.refl _ _
  | succ k ih =>
    intro hk
    have s := g3t P Dw (k + 1) b c d T B (hP.pos (k + 1) (by omega) hk)
    rw [Nat.add_sub_cancel] at s
    have t := (TimedLe.single (by rfl) s).trans (ih (by omega))
    rwa [Nat.add_comm 1] at t

include hP in
/-- One block of digit `0`. -/
theorem block_gen (b : ℕ) (hb : readTapeBit Dw b = true) (T B : List Bool) :
    TimedLe genTB (2 * pop + 3) (gc P Dw 1 0 b T.length B.length T B)
      (gc P Dw 1 0 (b + 1) (T ++ blk pop).length (B ++ blk pop).length (T ++ blk pop) (B ++ blk pop)) := by
  have s1 := g1t P Dw 0 b T B hb
  have w := inner_walk pop P Dw hP b (T ++ [true]) (B ++ [true]) pop le_rfl
  simp only [List.length_append, List.length_singleton] at w
  have s2 := g2f P Dw (1 + pop) b (T.length + 1 + pop) (B.length + 1 + pop)
    (T ++ [true] ++ List.replicate pop false) (B ++ [true] ++ List.replicate pop false) (hP.past (1 + pop) (by omega))
  rw [show 1 + pop - 1 = pop by omega] at s2
  have w2 := pop_rewind pop P Dw hP b (T.length + 1 + pop) (B.length + 1 + pop)
    (T ++ [true] ++ List.replicate pop false) (B ++ [true] ++ List.replicate pop false) pop le_rfl
  have s3 := g3f P Dw 0 b (T.length + 1 + pop) (B.length + 1 + pop)
    (T ++ [true] ++ List.replicate pop false) (B ++ [true] ++ List.replicate pop false) hP.zero
  have hTb : T ++ [true] ++ List.replicate pop false = T ++ blk pop := by
    rw [List.append_assoc]; rfl
  have hBb : B ++ [true] ++ List.replicate pop false = B ++ blk pop := by
    rw [List.append_assoc]; rfl
  have hlT : (T ++ blk pop).length = T.length + 1 + pop := by
    simp only [List.length_append, blk, List.length_cons, List.length_replicate]; omega
  have hlB : (B ++ blk pop).length = B.length + 1 + pop := by
    simp only [List.length_append, blk, List.length_cons, List.length_replicate]; omega
  rw [hTb, hBb] at s3
  rw [hTb, hBb] at w2 s2 w
  rw [hlT, hlB]
  exact ((TimedLe.single (by rfl) s1).trans (w.trans ((TimedLe.single (by rfl) s2).trans
    (w2.trans (TimedLe.single (by rfl) s3))))).mono (by omega)

include hP hDw in
theorem blocks_gen : ∀ j, j ≤ D → TimedLe genTB (j * (2 * pop + 3)) (gc P Dw 1 0 1 1 0 [false] [])
    (gc P Dw 1 0 (1 + j) (1 + j * (pop + 1)) (j * (pop + 1)) (false :: blks pop j) (blks pop j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.zero_mul, Nat.add_zero]
    exact TimedLe.refl _ _
  | succ j ih =>
    intro hj
    have hl1 : (false :: blks pop j).length = 1 + j * (pop + 1) := by
      rw [List.length_cons, blks_length]; omega
    have hl2 : (blks pop j).length = j * (pop + 1) := blks_length pop j
    have b := block_gen pop P Dw hP (1 + j) (hDw.pos (1 + j) (by omega) (by omega)) (false :: blks pop j) (blks pop j)
    rw [hl1, hl2] at b
    have e1 : (false :: blks pop j) ++ blk pop = false :: blks pop (j + 1) := by rw [blks_succ]; rfl
    rw [e1, ← blks_succ] at b
    have hl3 : (false :: blks pop (j + 1)).length = 1 + (j + 1) * (pop + 1) := by
      rw [List.length_cons, blks_length]; omega
    rw [hl3, blks_length, show 1 + j + 1 = 1 + (j + 1) by omega] at b
    exact ((ih (by omega)).trans b).mono
      (by rw [show (j + 1) * (2 * pop + 3) = j * (2 * pop + 3) + (2 * pop + 3) from Nat.succ_mul j _])

include hDw in
theorem dw_rewind (a c d : ℕ) (T B : List Bool) :
    ∀ k, k ≤ D → TimedLe genTB k (gc P Dw 6 a k c d T B) (gc P Dw 6 a 0 c d T B) := by
  intro k
  induction k with
  | zero => intro _; exact TimedLe.refl _ _
  | succ k ih =>
    intro hk
    have s := g6t P Dw a (k + 1) c d T B (hDw.pos (k + 1) (by omega) hk)
    rw [Nat.add_sub_cancel] at s
    have t := (TimedLe.single (by rfl) s).trans (ih (by omega))
    rwa [Nat.add_comm 1] at t

theorem ltb_rewind (a b : ℕ) (T B : List Bool) :
    ∀ k, TimedLe genTB k (gc P Dw 7 a b k (k + 1) T B) (gc P Dw 7 a b 0 1 T B) := by
  intro k
  induction k with
  | zero => exact TimedLe.refl _ _
  | succ k ih =>
    have s := g7f P Dw a b (k + 1) (k + 1 + 1) T B (marker_read (k + 1) (by omega))
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel] at s
    have t := (TimedLe.single (by rfl) s).trans ih
    rwa [Nat.add_comm 1] at t

end GenWalks

/-- `genTB`'s step budget. -/
def genCost (pop D : ℕ) : ℕ := 1 + D * (2 * pop + 3) + 3 + D + 1 + (1 + D * (pop + 1)) + 1

/-- **The static tapes of code `0`.** -/
theorem genTB_run (pop D : ℕ) (P Dw : List Bool) (hP : ReadsWord P pop) (hDw : ReadsWord Dw D) :
    Step genTB (genCost pop D) (fun _ => 0) ![P, Dw, [], [], []] (fun _ => 0)
      ![P, Dw, [true], Tt (pop + 1) (List.replicate D 0), Bt (pop + 1) D] := by
  have s0 := g0 P Dw
  have w := blocks_gen pop D P Dw hP hDw D le_rfl
  have hl : (blks pop D).length = D * (pop + 1) := blks_length pop D
  have s1 := g1f P Dw 0 (1 + D) (1 + D * (pop + 1)) (false :: blks pop D) (blks pop D) (hDw.past (1 + D) (by omega))
  rw [hl] at s1
  have s2 := g4 P Dw 0 (1 + D) (1 + D * (pop + 1)) (false :: blks pop D) (blks pop D ++ [true])
  rw [List.length_append, hl, List.length_singleton, List.append_assoc] at s2
  have s3 := g5 P Dw 0 (1 + D) (1 + D * (pop + 1)) (D * (pop + 1) + 1 + 1) (false :: blks pop D)
    (blks pop D ++ ([true] ++ [true]))
  rw [show 1 + D - 1 = D by omega] at s3
  have w2 := dw_rewind D P Dw hDw 0 (1 + D * (pop + 1)) (D * (pop + 1) + 1 + 1) (false :: blks pop D)
    (blks pop D ++ ([true] ++ [true])) D le_rfl
  have s4 := g6f P Dw 0 0 (1 + D * (pop + 1)) (D * (pop + 1) + 1 + 1) (false :: blks pop D)
    (blks pop D ++ ([true] ++ [true])) hDw.zero
  have w3 := ltb_rewind P Dw 0 0 (false :: blks pop D) (blks pop D ++ ([true] ++ [true])) (1 + D * (pop + 1))
  rw [show 1 + D * (pop + 1) + 1 = D * (pop + 1) + 1 + 1 by omega] at w3
  have s5 := g7t P Dw 0 0 1 (false :: blks pop D) (blks pop D ++ ([true] ++ [true]))
  have all := (TimedLe.single (by rfl) s0).trans (w.trans ((TimedLe.single (by rfl) s1).trans
    ((TimedLe.single (by rfl) s2).trans ((TimedLe.single (by rfl) s3).trans (w2.trans
      ((TimedLe.single (by rfl) s4).trans (w3.trans (TimedLe.single (by rfl) s5))))))))
  have st := (all.mono (show _ ≤ genCost pop D by unfold genCost; omega)).toStep (by rfl)
  rw [Tt_zeros, Bt_zeros]
  refine st.congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · rfl

/-! ## `ucopy`: copy a unary word exactly -/

def ucopy (skip park : Bool) : Machine 2 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 6
  rule := fun q sc =>
    if q.val = 0 then some ⟨if skip then 1 else 2, ![none, some false], ![.right, .right]⟩
    else if q.val = 1 then some ⟨2, ![none, none], ![.right, .stay]⟩
    else if q.val = 2 then some (if sc 0 then ⟨2, ![none, some true], ![.right, .right]⟩
      else ⟨3, ![none, none], ![.left, .stay]⟩)
    else if q.val = 3 then some (if sc 0 then ⟨3, ![none, none], ![.left, .stay]⟩
      else ⟨4, ![none, none], ![.stay, .left]⟩)
    else if q.val = 4 then some (if sc 1 then ⟨4, ![none, none], ![.stay, .left]⟩
      else ⟨if park then 5 else 6, ![none, none], ![.stay, .stay]⟩)
    else if q.val = 5 then some ⟨6, ![none, none], ![.stay, .right]⟩
    else none

def uc (I : List Bool) (q : Fin 7) (a b : ℕ) (O : List Bool) : Configuration 2 7 := ⟨q, ![a, b], ![I, O]⟩

section UTrans
variable (skip park : Bool) (I : List Bool)

theorem u0 : LocalBitMultitape.step (ucopy skip park) (uc I 0 0 0 []) =
    some (uc I (if skip then 1 else 2) 1 1 [false]) := by
  simp [LocalBitMultitape.step, ucopy, uc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem u1 (a b : ℕ) (O : List Bool) :
    LocalBitMultitape.step (ucopy skip park) (uc I 1 a b O) = some (uc I 2 (a + 1) b O) := by
  simp [LocalBitMultitape.step, ucopy, uc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem u2t (a : ℕ) (O : List Bool) (h : readTapeBit I a = true) :
    LocalBitMultitape.step (ucopy skip park) (uc I 2 a O.length O) = some (uc I 2 (a + 1) (O.length + 1) (O ++ [true])) := by
  simp [LocalBitMultitape.step, ucopy, uc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, Streaming.write_append]

theorem u2f (a b : ℕ) (O : List Bool) (h : readTapeBit I a = false) :
    LocalBitMultitape.step (ucopy skip park) (uc I 2 a b O) = some (uc I 3 (a - 1) b O) := by
  simp [LocalBitMultitape.step, ucopy, uc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem u3t (a b : ℕ) (O : List Bool) (h : readTapeBit I a = true) :
    LocalBitMultitape.step (ucopy skip park) (uc I 3 a b O) = some (uc I 3 (a - 1) b O) := by
  simp [LocalBitMultitape.step, ucopy, uc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem u3f (a b : ℕ) (O : List Bool) (h : readTapeBit I a = false) :
    LocalBitMultitape.step (ucopy skip park) (uc I 3 a b O) = some (uc I 4 a (b - 1) O) := by
  simp [LocalBitMultitape.step, ucopy, uc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem u4t (a b : ℕ) (O : List Bool) (h : readTapeBit O b = true) :
    LocalBitMultitape.step (ucopy skip park) (uc I 4 a b O) = some (uc I 4 a (b - 1) O) := by
  simp [LocalBitMultitape.step, ucopy, uc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem u4f (a b : ℕ) (O : List Bool) (h : readTapeBit O b = false) :
    LocalBitMultitape.step (ucopy skip park) (uc I 4 a b O) = some (uc I (if park then 5 else 6) a b O) := by
  simp [LocalBitMultitape.step, ucopy, uc, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem u5 (a b : ℕ) (O : List Bool) :
    LocalBitMultitape.step (ucopy skip park) (uc I 5 a b O) = some (uc I 6 a (b + 1) O) := by
  simp [LocalBitMultitape.step, ucopy, uc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

end UTrans

section UWalks
variable (skip park : Bool) (I : List Bool)

theorem ucopy_walk (s X : ℕ) (hI : ∀ i, s ≤ i → i < s + X → readTapeBit I i = true) :
    ∀ j, j ≤ X → TimedLe (ucopy skip park) j (uc I 2 s 1 [false])
      (uc I 2 (s + j) (1 + j) (false :: List.replicate j true)) := by
  intro j
  induction j with
  | zero => intro _; exact TimedLe.refl _ _
  | succ j ih =>
    intro hj
    have s1 := u2t skip park I (s + j) (false :: List.replicate j true) (hI (s + j) (by omega) (by omega))
    simp only [List.length_cons, List.length_replicate, List.cons_append, ← List.replicate_succ'] at s1
    rw [show s + j + 1 = s + (j + 1) by omega, show j + 1 + 1 = 1 + (j + 1) by omega] at s1
    rw [show 1 + j = j + 1 by omega] at ih
    exact (ih (by omega)).trans (TimedLe.single (by rfl) s1)

theorem uin_rewind (b : ℕ) (O : List Bool) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → readTapeBit I i = true) → TimedLe (ucopy skip park) k (uc I 3 k b O) (uc I 3 0 b O) := by
  intro k
  induction k with
  | zero => intro _; exact TimedLe.refl _ _
  | succ k ih =>
    intro hk
    have s := u3t skip park I (k + 1) b O (hk (k + 1) (by omega) le_rfl)
    rw [Nat.add_sub_cancel] at s
    have t := (TimedLe.single (by rfl) s).trans (ih (fun i h1 h2 => hk i h1 (by omega)))
    rwa [Nat.add_comm 1] at t

theorem uout_rewind (a : ℕ) (O : List Bool) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → readTapeBit O i = true) → TimedLe (ucopy skip park) k (uc I 4 a k O) (uc I 4 a 0 O) := by
  intro k
  induction k with
  | zero => intro _; exact TimedLe.refl _ _
  | succ k ih =>
    intro hk
    have s := u4t skip park I a (k + 1) O (hk (k + 1) (by omega) le_rfl)
    rw [Nat.add_sub_cancel] at s
    have t := (TimedLe.single (by rfl) s).trans (ih (fun i h1 h2 => hk i h1 (by omega)))
    rwa [Nat.add_comm 1] at t

end UWalks

/-- `ucopy`'s step budget. -/
def ucopyCost (X : ℕ) : ℕ := 3 * X + 10

/-- **Exact copy of a unary word.** The input reads as `word (X + [skip])`; the blank output becomes
`CompareMachine.word X`; heads back at `0` (the output's at `1` if `park`). -/
theorem ucopy_run (skip park : Bool) (I : List Bool) (X : ℕ) (hI : ReadsWord I (X + if skip then 1 else 0)) :
    Step (ucopy skip park) (ucopyCost X) (fun _ => 0) ![I, []] ![0, if park then 1 else 0]
      ![I, CompareMachine.word X] := by
  have hY := hI
  set Y := X + (if skip then 1 else 0) with hYdef
  set s := (if skip then 2 else 1) with hs
  have hsY : s + X = Y + 1 := by rw [hs, hYdef]; split <;> omega
  -- the start (and the skip)
  have t0 : TimedLe (ucopy skip park) (if skip then 2 else 1) (uc I 0 0 0 []) (uc I 2 s 1 [false]) := by
    have a := u0 skip park I
    cases skip
    · simp only [Bool.false_eq_true, if_false] at a hs ⊢
      rw [hs]
      exact TimedLe.single (by rfl) a
    · simp only [if_true] at a hs ⊢
      rw [hs]
      exact (TimedLe.single (by rfl) a).trans (TimedLe.single (by rfl) (u1 true park I 1 1 [false]))
  have w := ucopy_walk skip park I s X (fun i h1 h2 => hI.pos i (by rw [hs] at h1; split at h1 <;> omega)
    (by omega)) X le_rfl
  have s1 := u2f skip park I (s + X) (1 + X) (false :: List.replicate X true) (hI.past (s + X) (by omega))
  rw [show s + X - 1 = Y by omega] at s1
  have w2 := uin_rewind skip park I (1 + X) (false :: List.replicate X true) Y (fun i h1 h2 => hI.pos i h1 h2)
  have s2 := u3f skip park I 0 (1 + X) (false :: List.replicate X true) hI.zero
  rw [show 1 + X - 1 = X by omega] at s2
  have hw : ReadsWord (false :: List.replicate X true) X := readsWord_word X
  have w3 := uout_rewind skip park I 0 (false :: List.replicate X true) X (fun i h1 h2 => hw.pos i h1 h2)
  have s3 := u4f skip park I 0 0 (false :: List.replicate X true) hw.zero
  have hY1 : Y ≤ X + 1 := by rw [hYdef]; split <;> omega
  cases park
  · simp only [Bool.false_eq_true, if_false] at s3 ⊢
    have all := t0.trans (w.trans ((TimedLe.single (by rfl) s1).trans (w2.trans ((TimedLe.single (by rfl) s2).trans
      (w3.trans (TimedLe.single (by rfl) s3))))))
    have st := (all.mono (show _ ≤ ucopyCost X by unfold ucopyCost; split <;> omega)).toStep (by rfl)
    exact (st.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  · simp only [if_true] at s3 ⊢
    have s4 := u5 skip true I 0 0 (false :: List.replicate X true)
    have all := t0.trans (w.trans ((TimedLe.single (by rfl) s1).trans (w2.trans ((TimedLe.single (by rfl) s2).trans
      (w3.trans ((TimedLe.single (by rfl) s3).trans (TimedLe.single (by rfl) s4)))))))
    have st := (all.mono (show _ ≤ ucopyCost X by unfold ucopyCost; split <;> omega)).toStep (by rfl)
    exact (st.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl

end NearCubicWires.PacketsCombine.Tab

