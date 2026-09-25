import Proof.Packets.PacketsCombineTabMicro

/-! # P2 (iii) table writer, part 2: the odometer on the one-hot tuple tape

Consumer: the THR selection-table writer (`ThrMeta`'s tape 15), which lists the digit tuples of every
code `c < (pop+1)^digits` in ascending order (A.13.7, `paper.tex:3113-3142`; `T_prep`,
`paper.tex:1197-1200`). One run of `odo` turns the tuple tape of code `c` into that of code `c+1`
(`incr_digitsOf`), so the writer never divides.

Tapes (all heads move together): `0` the marker `[true]`, `1` the tuple tape `false :: blocksOf m ds`
(one-hot blocks, little-endian digits), `2` the static block-end tape `true :: (bm m)^D ++ [true]`
(`bm m = false^(m-1) true`; the leading `true` is the end of "block `-1`", the trailing one the end of
the whole tape). States: `0` start, `1` scan for the set bit, `2` set the next cell, `3`/`4`/`5` carry
(back to the block start, set it, forward to the block end), `6` rewind to the marker, `7` halt.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

/-! ## The static tapes -/

/-- The block-end marks of one block of width `m`. -/
def bm (m : ℕ) : List Bool := List.replicate (m - 1) false ++ [true]

/-- The static block-end tape of `D` blocks. -/
def Bt (m D : ℕ) : List Bool := true :: ((List.replicate D (bm m)).flatten ++ [true])

/-- The tuple tape of a digit list. -/
def Tt (m : ℕ) (ds : List ℕ) : List Bool := false :: blocksOf m ds

theorem bm_length (m : ℕ) (hm : 1 ≤ m) : (bm m).length = m := by
  simp only [bm, List.length_append, List.length_replicate, List.length_singleton]; omega

theorem bm_getD (m v : ℕ) (hm : 1 ≤ m) (hv : v < m) : (bm m).getD v false = decide (v + 1 = m) := by
  unfold bm
  by_cases h : v < m - 1
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
      List.getElem_replicate]
    symm; rw [decide_eq_false_iff_not]; omega
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
    simp only [List.length_replicate, show v - (m - 1) = 0 by omega]
    exact (decide_eq_true (by omega : v + 1 = m)).symm

theorem flatten_replicate_getD (L : List Bool) : ∀ D j v, j < D → v < L.length →
    (List.replicate D L).flatten.getD (j * L.length + v) false = L.getD v false := by
  intro D
  induction D with
  | zero => intro j v hj; omega
  | succ D ih =>
    intro j v hj hv
    rw [List.replicate_succ, List.flatten_cons]
    rcases j with _ | j
    · rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ hv]
    · rw [List.getD_append_right _ _ _ _ (by rw [Nat.succ_mul]; omega)]
      rw [show (j + 1) * L.length + v - L.length = j * L.length + v by rw [Nat.succ_mul]; omega]
      exact ih j v (by omega) hv

theorem flatten_replicate_length (L : List Bool) (D : ℕ) : (List.replicate D L).flatten.length = D * L.length := by
  induction D with
  | zero => simp
  | succ D ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul, Nat.add_comm]

theorem Bt_read (m D j v : ℕ) (hm : 1 ≤ m) (hj : j < D) (hv : v < m) :
    readTapeBit (Bt m D) (1 + j * m + v) = decide (v + 1 = m) := by
  unfold Bt readTapeBit
  rw [show 1 + j * m + v = (j * m + v) + 1 by omega, List.getD_cons_succ]
  have hl := bm_length m hm
  rw [List.getD_append _ _ _ _ (by rw [flatten_replicate_length, hl]; nlinarith)]
  have h := flatten_replicate_getD (bm m) D j v hj (by rw [hl]; exact hv)
  rw [hl] at h
  rw [h, bm_getD m v hm hv]

theorem Bt_read_start (m D j : ℕ) (hm : 1 ≤ m) (hj : j ≤ D) : readTapeBit (Bt m D) (j * m) = true := by
  rcases j with _ | j
  · rw [Nat.zero_mul]; rfl
  · have h := Bt_read m D j (m - 1) hm (by omega) (by omega)
    rw [show 1 + j * m + (m - 1) = (j + 1) * m by rw [Nat.succ_mul]; omega] at h
    rw [h]; simp only [decide_eq_true_eq]; omega

theorem Bt_read_end (m D : ℕ) (hm : 1 ≤ m) : readTapeBit (Bt m D) (1 + D * m) = true := by
  unfold Bt readTapeBit
  rw [show 1 + D * m = D * m + 1 by omega, List.getD_cons_succ]
  have hl : (List.replicate D (bm m)).flatten.length = D * m := by rw [flatten_replicate_length, bm_length m hm]
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
  rfl

/-! ## Reading and writing one block of the tuple tape -/

theorem blocksOf_append (m : ℕ) (zs ys : List ℕ) : blocksOf m (zs ++ ys) = blocksOf m zs ++ blocksOf m ys := by
  simp only [blocksOf, List.map_append, List.flatten_append]

theorem Tt_split (m : ℕ) (zs : List ℕ) (x : ℕ) (ys : List ℕ) :
    Tt m (zs ++ x :: ys) = false :: (blocksOf m zs ++ (oneHot m x ++ blocksOf m ys)) := by
  rw [Tt, blocksOf_append, blocksOf_cons]

theorem writeTapeBit_set : ∀ (l : List Bool) (pos : ℕ) (b : Bool), pos < l.length → writeTapeBit l pos b = l.set pos b := by
  intro l
  induction l with
  | nil => intro pos b h; simp at h
  | cons a l ih =>
    intro pos b h
    rcases pos with _ | pos
    · rfl
    · simp only [writeTapeBit, List.set_cons_succ]
      rw [ih pos b (by simp at h; omega)]

theorem mid_read (m : ℕ) (zs : List ℕ) (M R : List Bool) (v : ℕ) (hv : v < M.length) :
    readTapeBit (false :: (blocksOf m zs ++ (M ++ R))) (1 + zs.length * m + v) = M.getD v false := by
  unfold readTapeBit
  rw [show 1 + zs.length * m + v = zs.length * m + v + 1 by omega, List.getD_cons_succ,
    List.getD_append_right _ _ _ _ (by rw [blocksOf_length]; omega), blocksOf_length,
    show zs.length * m + v - zs.length * m = v by omega, List.getD_append _ _ _ _ hv]

theorem mid_write (m : ℕ) (zs : List ℕ) (M R : List Bool) (v : ℕ) (hv : v < M.length) (b : Bool) :
    writeTapeBit (false :: (blocksOf m zs ++ (M ++ R))) (1 + zs.length * m + v) b =
      false :: (blocksOf m zs ++ (M.set v b ++ R)) := by
  rw [writeTapeBit_set _ _ _ (by simp only [List.length_cons, List.length_append, blocksOf_length]; omega),
    show 1 + zs.length * m + v = zs.length * m + v + 1 by omega, List.set_cons_succ,
    List.set_append_right _ _ (by rw [blocksOf_length]; omega), blocksOf_length,
    show zs.length * m + v - zs.length * m = v by omega, List.set_append_left _ _ hv]

theorem oneHot_getD (m x v : ℕ) (hv : v < m) : (oneHot m x).getD v false = decide (x = v) := by
  rw [List.getD_eq_getElem _ _ (by rw [oneHot_length]; exact hv)]
  simp only [oneHot, List.getElem_ofFn]

theorem oneHot_clear (m x : ℕ) : (oneHot m x).set x false = List.replicate m false := by
  apply List.ext_getElem (by simp [oneHot])
  intro i h1 _
  rw [List.getElem_set, List.getElem_replicate]
  simp only [oneHot, List.getElem_ofFn]
  split_ifs with h
  · rfl
  · simp only [decide_eq_false_iff_not]; omega

theorem oneHot_getElem (m x i : ℕ) (h : i < (oneHot m x).length) : (oneHot m x)[i] = decide (x = i) := by
  have e := oneHot_getD m x i (by rw [oneHot_length] at h; exact h)
  rwa [List.getD_eq_getElem _ _ h] at e

theorem oneHot_mark (m v : ℕ) (_hv : v < m) : (List.replicate m false).set v true = oneHot m v := by
  apply List.ext_getElem (by simp [oneHot])
  intro i h1 h2
  rw [List.getElem_set, List.getElem_replicate, oneHot_getElem m v i h2]
  split_ifs with h
  · exact (decide_eq_true h).symm
  · exact (decide_eq_false h).symm

theorem Tt_read_end (m : ℕ) (ds : List ℕ) : readTapeBit (Tt m ds) (1 + ds.length * m) = false := by
  unfold readTapeBit Tt
  rw [show 1 + ds.length * m = ds.length * m + 1 by omega, List.getD_cons_succ,
    List.getD_eq_default _ _ (by rw [blocksOf_length])]

/-! ## The machine -/

/-- Write `b` on the tuple tape only. -/
def wT (b : Bool) : Fin 3 → Option Bool := fun i => if i.val = 1 then some b else none

def odo : Machine 3 8 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 7
  rule := fun q scan =>
    if q.val = 0 then some ⟨1, fun _ => none, fun _ => .right⟩
    else if q.val = 1 then
      some (if scan 1 then (if scan 2 then ⟨3, wT false, fun _ => .left⟩ else ⟨2, wT false, fun _ => .right⟩)
        else (if scan 2 then ⟨6, fun _ => none, fun _ => .stay⟩ else ⟨1, fun _ => none, fun _ => .right⟩))
    else if q.val = 2 then some ⟨6, wT true, fun _ => .stay⟩
    else if q.val = 3 then
      some (if scan 2 then ⟨4, fun _ => none, fun _ => .right⟩ else ⟨3, fun _ => none, fun _ => .left⟩)
    else if q.val = 4 then some ⟨5, wT true, fun _ => .stay⟩
    else if q.val = 5 then
      some (if scan 2 then ⟨1, fun _ => none, fun _ => .right⟩ else ⟨5, fun _ => none, fun _ => .right⟩)
    else if q.val = 6 then
      some (if scan 0 then ⟨7, fun _ => none, fun _ => .stay⟩ else ⟨6, fun _ => none, fun _ => .left⟩)
    else none

def ocfg (q : Fin 8) (h : ℕ) (T B : List Bool) : Configuration 3 8 := ⟨q, fun _ => h, ![[true], T, B]⟩

/-! ## Transitions -/

theorem o_start (T B : List Bool) : LocalBitMultitape.step odo (ocfg 0 0 T B) = some (ocfg 1 1 T B) := by
  simp [LocalBitMultitape.step, odo, ocfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem o_scan (T B : List Bool) (h : ℕ) (hT : readTapeBit T h = false) (hB : readTapeBit B h = false) :
    LocalBitMultitape.step odo (ocfg 1 h T B) = some (ocfg 1 (h + 1) T B) := by
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hT, hB]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem o_done (T B : List Bool) (h : ℕ) (hT : readTapeBit T h = false) (hB : readTapeBit B h = true) :
    LocalBitMultitape.step odo (ocfg 1 h T B) = some (ocfg 6 h T B) := by
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hT, hB]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem o_hit (T B : List Bool) (h : ℕ) (hT : readTapeBit T h = true) (hB : readTapeBit B h = false) :
    LocalBitMultitape.step odo (ocfg 1 h T B) = some (ocfg 2 (h + 1) (writeTapeBit T h false) B) := by
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hT, hB]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem o_carry (T B : List Bool) (h : ℕ) (hT : readTapeBit T h = true) (hB : readTapeBit B h = true) :
    LocalBitMultitape.step odo (ocfg 1 h T B) = some (ocfg 3 (h - 1) (writeTapeBit T h false) B) := by
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hT, hB]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem o_set (T B : List Bool) (h : ℕ) :
    LocalBitMultitape.step odo (ocfg 2 h T B) = some (ocfg 6 h (writeTapeBit T h true) B) := by
  simp [LocalBitMultitape.step, odo, ocfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem o_back (T B : List Bool) (h : ℕ) (hB : readTapeBit B h = false) :
    LocalBitMultitape.step odo (ocfg 3 h T B) = some (ocfg 3 (h - 1) T B) := by
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hB]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem o_back_end (T B : List Bool) (h : ℕ) (hB : readTapeBit B h = true) :
    LocalBitMultitape.step odo (ocfg 3 h T B) = some (ocfg 4 (h + 1) T B) := by
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hB]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem o_bw (T B : List Bool) (h : ℕ) :
    LocalBitMultitape.step odo (ocfg 4 h T B) = some (ocfg 5 h (writeTapeBit T h true) B) := by
  simp [LocalBitMultitape.step, odo, ocfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem o_fwd (T B : List Bool) (h : ℕ) (hB : readTapeBit B h = false) :
    LocalBitMultitape.step odo (ocfg 5 h T B) = some (ocfg 5 (h + 1) T B) := by
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hB]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem o_fwd_end (T B : List Bool) (h : ℕ) (hB : readTapeBit B h = true) :
    LocalBitMultitape.step odo (ocfg 5 h T B) = some (ocfg 1 (h + 1) T B) := by
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hB]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem o_rew (T B : List Bool) (h : ℕ) :
    LocalBitMultitape.step odo (ocfg 6 (h + 1) T B) = some (ocfg 6 h T B) := by
  have hL : readTapeBit [true] (h + 1) = false := rfl
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hL]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem o_halt (T B : List Bool) :
    LocalBitMultitape.step odo (ocfg 6 0 T B) = some (ocfg 7 0 T B) := by
  have hL : readTapeBit [true] 0 = true := rfl
  simp [LocalBitMultitape.step, odo, ocfg, Configuration.scanned, hL]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

/-! ## Walks -/

theorem scan_walk (T B : List Bool) (b : ℕ) : ∀ x, (∀ u, u < x → readTapeBit T (b + u) = false) →
    (∀ u, u < x → readTapeBit B (b + u) = false) → TimedLe odo x (ocfg 1 b T B) (ocfg 1 (b + x) T B) := by
  intro x
  induction x with
  | zero => intro _ _; exact TimedLe.refl _ _
  | succ x ih =>
    intro hT hB
    exact (ih (fun u hu => hT u (by omega)) (fun u hu => hB u (by omega))).trans
      (TimedLe.single (by rfl) (o_scan T B (b + x) (hT x (by omega)) (hB x (by omega))))

theorem back_walk (T B : List Bool) (b : ℕ) : ∀ u, (∀ k, 1 ≤ k → k ≤ u → readTapeBit B (b + k) = false) →
    TimedLe odo u (ocfg 3 (b + u) T B) (ocfg 3 b T B) := by
  intro u
  induction u with
  | zero => intro _; exact TimedLe.refl _ _
  | succ u ih =>
    intro hB
    have hs := o_back T B (b + (u + 1)) (hB (u + 1) (by omega) le_rfl)
    rw [show b + (u + 1) - 1 = b + u by omega] at hs
    have h := (TimedLe.single (by rfl) hs).trans (ih (fun k h1 h2 => hB k h1 (by omega)))
    rwa [Nat.add_comm 1] at h

theorem fwd_walk (T B : List Bool) (b : ℕ) : ∀ x, (∀ u, u < x → readTapeBit B (b + u) = false) →
    TimedLe odo x (ocfg 5 b T B) (ocfg 5 (b + x) T B) := by
  intro x
  induction x with
  | zero => intro _; exact TimedLe.refl _ _
  | succ x ih =>
    intro hB
    exact (ih (fun u hu => hB u (by omega))).trans (TimedLe.single (by rfl) (o_fwd T B (b + x) (hB x (by omega))))

theorem rew_walk (T B : List Bool) : ∀ h, TimedLe odo (h + 1) (ocfg 6 h T B) (ocfg 7 0 T B) := by
  intro h
  induction h with
  | zero => exact TimedLe.single (by rfl) (o_halt T B)
  | succ h ih =>
    have t := (TimedLe.single (by rfl) (o_rew T B h)).trans ih
    rwa [Nat.add_comm 1] at t

/-! ## One block -/

/-- The carry through one block, over an arbitrary prefix `zs` of `j` blocks. -/
theorem carry_core (m D : ℕ) (hm : 1 ≤ m) (zs ys : List ℕ) (hjD : zs.length < D) :
    TimedLe odo (3 * m + 1)
      (ocfg 1 (1 + zs.length * m) (false :: (blocksOf m zs ++ (oneHot m (m - 1) ++ blocksOf m ys))) (Bt m D))
      (ocfg 1 (1 + (zs.length + 1) * m) (false :: (blocksOf m zs ++ (oneHot m 0 ++ blocksOf m ys))) (Bt m D)) := by
  -- scan to the set bit at `m-1`
  have t1 := scan_walk (false :: (blocksOf m zs ++ (oneHot m (m - 1) ++ blocksOf m ys))) (Bt m D)
    (1 + zs.length * m) (m - 1)
    (fun u hu => by
      rw [mid_read m zs _ _ u (by rw [oneHot_length]; omega), oneHot_getD m _ u (by omega)]
      simp only [decide_eq_false_iff_not]; omega)
    (fun u hu => by
      rw [Bt_read m D zs.length u hm hjD (by omega)]
      simp only [decide_eq_false_iff_not]; omega)
  -- the carry transition
  have hT1 : readTapeBit (false :: (blocksOf m zs ++ (oneHot m (m - 1) ++ blocksOf m ys)))
      (1 + zs.length * m + (m - 1)) = true := by
    rw [mid_read m zs _ _ (m - 1) (by rw [oneHot_length]; omega), oneHot_getD m _ _ (by omega)]
    simp
  have hB1 : readTapeBit (Bt m D) (1 + zs.length * m + (m - 1)) = true := by
    rw [Bt_read m D zs.length (m - 1) hm hjD (by omega)]
    simp only [decide_eq_true_eq]; omega
  have s2 := o_carry _ _ _ hT1 hB1
  rw [mid_write m zs _ _ (m - 1) (by rw [oneHot_length]; omega), oneHot_clear,
    show 1 + zs.length * m + (m - 1) - 1 = zs.length * m + (m - 1) by omega] at s2
  have t2 := TimedLe.single (by rfl) s2
  -- back to the block start
  have t3 := back_walk (false :: (blocksOf m zs ++ (List.replicate m false ++ blocksOf m ys))) (Bt m D)
    (zs.length * m) (m - 1)
    (fun k h1 h2 => by
      rw [show zs.length * m + k = 1 + zs.length * m + (k - 1) by omega,
        Bt_read m D zs.length (k - 1) hm hjD (by omega)]
      simp only [decide_eq_false_iff_not]; omega)
  have s4 := o_back_end (false :: (blocksOf m zs ++ (List.replicate m false ++ blocksOf m ys))) (Bt m D)
    (zs.length * m) (Bt_read_start m D zs.length hm (by omega))
  rw [show zs.length * m + 1 = 1 + zs.length * m + 0 by omega] at s4
  have t4 := TimedLe.single (by rfl) s4
  -- set the block's first cell
  have s5 := o_bw (false :: (blocksOf m zs ++ (List.replicate m false ++ blocksOf m ys))) (Bt m D)
    (zs.length * m + 1)
  rw [show zs.length * m + 1 = 1 + zs.length * m + 0 by omega,
    mid_write m zs _ _ 0 (by rw [List.length_replicate]; omega), oneHot_mark m 0 (by omega)] at s5
  have t5 := TimedLe.single (by rfl) s5
  -- forward to the block end and on
  have t6 := fwd_walk (false :: (blocksOf m zs ++ (oneHot m 0 ++ blocksOf m ys))) (Bt m D)
    (1 + zs.length * m + 0) (m - 1)
    (fun u hu => by
      rw [Nat.add_zero, Bt_read m D zs.length u hm hjD (by omega)]
      simp only [decide_eq_false_iff_not]; omega)
  have s7 := o_fwd_end (false :: (blocksOf m zs ++ (oneHot m 0 ++ blocksOf m ys))) (Bt m D)
    (1 + zs.length * m + 0 + (m - 1))
    (by
      rw [Nat.add_zero, Bt_read m D zs.length (m - 1) hm hjD (by omega)]
      simp only [decide_eq_true_eq]; omega)
  rw [show 1 + zs.length * m + 0 + (m - 1) + 1 = 1 + (zs.length + 1) * m by rw [Nat.succ_mul]; omega] at s7
  have t7 := TimedLe.single (by rfl) s7
  exact (t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans t7)))))).mono (by omega)

/-- A carried block (digit `m-1`) becomes digit `0`; the scan moves on to the next block. -/
theorem carry_block (m D j : ℕ) (hm : 1 ≤ m) (ys : List ℕ) (hD : j + 1 + ys.length = D) :
    TimedLe odo (3 * m + 1) (ocfg 1 (1 + j * m) (Tt m (List.replicate j 0 ++ (m - 1) :: ys)) (Bt m D))
      (ocfg 1 (1 + (j + 1) * m) (Tt m (List.replicate (j + 1) 0 ++ ys)) (Bt m D)) := by
  have hzl : (List.replicate j 0).length = j := List.length_replicate
  have hT' : Tt m (List.replicate (j + 1) 0 ++ ys) =
      false :: (blocksOf m (List.replicate j 0) ++ (oneHot m 0 ++ blocksOf m ys)) := by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append, Tt_split]
  rw [Tt_split, hT']
  have h := carry_core m D hm (List.replicate j 0) ys (by rw [hzl]; omega)
  rw [hzl] at h
  exact h

/-- A block with digit `x < m-1` becomes `x+1`; the machine then rewinds. -/
theorem set_block (m D j x : ℕ) (hm : 1 ≤ m) (hx : x + 1 < m) (ys : List ℕ) (hD : j + 1 + ys.length = D) :
    TimedLe odo (m + 1) (ocfg 1 (1 + j * m) (Tt m (List.replicate j 0 ++ x :: ys)) (Bt m D))
      (ocfg 6 (1 + j * m + (x + 1)) (Tt m (List.replicate j 0 ++ (x + 1) :: ys)) (Bt m D)) := by
  set zs := List.replicate j 0 with hzs
  have hzl : zs.length = j := List.length_replicate
  have hjD : j < D := by omega
  rw [Tt_split, Tt_split]
  have t1 := scan_walk (false :: (blocksOf m zs ++ (oneHot m x ++ blocksOf m ys))) (Bt m D) (1 + j * m) x
    (fun u hu => by
      rw [← hzl, mid_read m zs _ _ u (by rw [oneHot_length]; omega), oneHot_getD m _ u (by omega)]
      simp only [decide_eq_false_iff_not]; omega)
    (fun u hu => by
      rw [Bt_read m D j u hm hjD (by omega)]; simp only [decide_eq_false_iff_not]; omega)
  have hT1 : readTapeBit (false :: (blocksOf m zs ++ (oneHot m x ++ blocksOf m ys))) (1 + j * m + x) = true := by
    rw [← hzl, mid_read m zs _ _ x (by rw [oneHot_length]; omega), oneHot_getD m _ _ (by omega)]
    simp
  have hB1 : readTapeBit (Bt m D) (1 + j * m + x) = false := by
    rw [Bt_read m D j x hm hjD (by omega)]; simp only [decide_eq_false_iff_not]; omega
  have t2 := TimedLe.single (by rfl) (o_hit _ _ _ hT1 hB1)
  rw [← hzl, mid_write m zs _ _ x (by rw [oneHot_length]; omega), oneHot_clear] at t2
  have t3 := TimedLe.single (by rfl) (o_set (false :: (blocksOf m zs ++ (List.replicate m false ++ blocksOf m ys)))
    (Bt m D) (1 + zs.length * m + x + 1))
  rw [show 1 + zs.length * m + x + 1 = 1 + zs.length * m + (x + 1) by omega,
    mid_write m zs _ _ (x + 1) (by simp only [List.length_replicate]; omega), oneHot_mark m (x + 1) hx] at t3
  rw [hzl] at t2 t3
  rw [show 1 + j * m + x + 1 = 1 + j * m + (x + 1) by omega] at t2
  exact (t1.trans (t2.trans t3)).mono (by omega)

/-! ## The whole increment -/

theorem scan_all (m D : ℕ) (hm : 1 ≤ m) : ∀ (ys : List ℕ) (j : ℕ), (∀ y ∈ ys, y < m) → j + ys.length = D →
    ∃ h', h' ≤ 1 + D * m ∧ TimedLe odo ((3 * m + 1) * ys.length + m + 1)
      (ocfg 1 (1 + j * m) (Tt m (List.replicate j 0 ++ ys)) (Bt m D))
      (ocfg 6 h' (Tt m (List.replicate j 0 ++ incr m ys)) (Bt m D)) := by
  intro ys
  induction ys with
  | nil =>
    intro j _ hD
    have hjD : j = D := by simpa using hD
    refine ⟨1 + j * m, by rw [hjD], ?_⟩
    have hT : readTapeBit (Tt m (List.replicate j 0 ++ [])) (1 + j * m) = false := by
      have h := Tt_read_end m (List.replicate j 0)
      rw [List.length_replicate] at h
      rw [List.append_nil]
      exact h
    have hB : readTapeBit (Bt m D) (1 + j * m) = true := by
      rw [hjD]; exact Bt_read_end m D hm
    exact (TimedLe.single (by rfl) (o_done _ _ _ hT hB)).mono (by simp)
  | cons x ys ih =>
    intro j hys hD
    have hx : x < m := hys x (List.mem_cons_self ..)
    simp only [List.length_cons] at hD
    by_cases hxm : x + 1 < m
    · refine ⟨1 + j * m + (x + 1), by nlinarith, ?_⟩
      simp only [incr, if_pos hxm]
      exact (set_block m D j x hm hxm ys (by omega)).mono (by simp only [List.length_cons]; nlinarith)
    · have hxe : x = m - 1 := by omega
      subst hxe
      obtain ⟨h', hh', t⟩ := ih (j + 1) (fun y hy => hys y (List.mem_cons_of_mem _ hy)) (by omega)
      refine ⟨h', hh', ?_⟩
      simp only [incr, if_neg hxm]
      have hs : List.replicate j 0 ++ 0 :: incr m ys = List.replicate (j + 1) 0 ++ incr m ys := by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [hs]
      exact ((carry_block m D j hm ys (by omega)).trans t).mono (by simp only [List.length_cons]; nlinarith)

/-- The step budget of one increment. -/
def odoBudget (m D : ℕ) : ℕ := 4 * (m + 1) * (D + 1) + 1 + D * m + 2

/-- **One odometer run: the tuple tape of `ds` becomes that of `incr m ds`, every head back at `0`.** -/
theorem odo_run (m D : ℕ) (hm : 1 ≤ m) (ds : List ℕ) (hds : ∀ y ∈ ds, y < m) (hD : ds.length = D) :
    Step odo (odoBudget m D) (fun _ => 0) ![[true], Tt m ds, Bt m D] (fun _ => 0)
      ![[true], Tt m (incr m ds), Bt m D] := by
  obtain ⟨h', hh', t⟩ := scan_all m D hm ds 0 hds (by omega)
  simp only [List.replicate_zero, List.nil_append, Nat.zero_mul, Nat.add_zero] at t
  have t0 := TimedLe.single (by rfl) (o_start (Tt m ds) (Bt m D))
  have all := (t0.trans (t.trans (rew_walk _ _ h'))).mono (show 1 + ((3 * m + 1) * ds.length + m + 1 + (h' + 1)) ≤
    odoBudget m D by unfold odoBudget; rw [hD]; nlinarith)
  exact all.toStep (by rfl)

end NearCubicWires.PacketsCombine.Tab

