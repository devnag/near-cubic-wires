import Proof.Packets.PacketsCombineTabRow

/-! # P2 (iii) table writer, part 4: one code's row, exactly

Consumer: the per-code body of the THR selection-table writer (`ThrMeta`'s tape 15,
`Proof/Packets/PacketsCombineThrLocal.lean`). `row_run`: on the tuple tape `Tt m ds` of the digit list `ds` (little-endian,
`D` digits `< m`) the row machine appends exactly `blocksOf m ds ++ [decide ((res + radixList ds 0) % p = 0)]`
(`= rowOf m D p res c` at `ds = digitsOf m D c`) and returns every other tape and head. Paper: A.13.7
(`paper.tex:3113-3142`): the acceptance bit is `modularTupleAccepts prime residue 2`; charged in `T_prep`
(`paper.tex:1197-1200`); budget class source-polynomial (`rowCost` is a fixed polynomial of `m, D, p, res`).
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

/-! ## Phase 1: copy the tuple cells to the output -/

theorem take_succ_getD (l : List Bool) (j : ℕ) (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l.getD j false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rfl

theorem copy_walk (W : RowTapes) (Bs : List Bool) (hT : W.T = false :: Bs) (K : ℕ) (hK : ReadsWord W.KW K)
    (hBs : Bs.length = K) (x y z : ℕ) (o : List Bool) :
    ∀ j, j ≤ K → TimedLe rowM j (rc W 1 1 x y z o) (rc W 1 (1 + j) x y z (o ++ Bs.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [List.take_zero, List.append_nil]
    exact TimedLe.refl _ _
  | succ j ih =>
    intro hj
    have s := r1c W (1 + j) x y z (o ++ Bs.take j) (hK.pos (1 + j) (by omega) (by omega))
    have hr : readTapeBit W.T (1 + j) = Bs.getD j false := by
      rw [hT]; unfold readTapeBit; rw [Nat.add_comm, List.getD_cons_succ]
    rw [hr, List.append_assoc, ← take_succ_getD Bs j (by omega), show 1 + j + 1 = 1 + (j + 1) by omega] at s
    exact (ih (by omega)).trans (TimedLe.single (by rfl) s)

/-- **Phase 1**: from the start to the Horner walk's first block boundary. -/
theorem phase1 (W : RowTapes) (Bs : List Bool) (hT : W.T = false :: Bs) (K : ℕ) (hK : ReadsWord W.KW K)
    (hBs : Bs.length = K) (x y z : ℕ) (o : List Bool) :
    TimedLe rowM (K + 2) (rc W 0 0 x y z o) (rc W 2 K x y z (o ++ Bs)) := by
  have s0 := r0 W 0 x y z o
  have w := copy_walk W Bs hT K hK hBs x y z o K le_rfl
  rw [← hBs, List.take_length, hBs] at w
  have s1 := r1e W (1 + K) x y z (o ++ Bs) (hK.past (1 + K) (by omega))
  rw [show 1 + K - 1 = K by omega] at s1
  exact ((TimedLe.single (by rfl) s0).trans (w.trans (TimedLe.single (by rfl) s1))).mono (by omega)

/-! ## Phase 2: one block (most significant first) -/

section Block
variable (W : RowTapes) (p : ℕ) (hp : 1 ≤ p) (hR : ReadsWord W.R (p - 1))
include hp hR

/-- Past the set bit: every cell adds `1` to `R` modulo `p`, down to the block boundary `b`. -/
theorem hs_walk (b : ℕ) (hBb : readTapeBit W.B b = true) (y z : ℕ) (o : List Bool) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → readTapeBit W.B (b + i) = false) → ∀ acc, acc < p →
      TimedLe rowM (k * (p + 2) + 1) (rc W 11 (b + k) acc y z o) (rc W 2 b ((acc + k) % p) y z o) := by
  intro k
  induction k with
  | zero =>
    intro _ acc hacc
    simp only [Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    rw [Nat.mod_eq_of_lt hacc]
    exact TimedLe.single (by rfl) (r11b W b acc y z o hBb)
  | succ k ih =>
    intro hk acc hacc
    have s1 := r11n W (b + (k + 1)) acc y z o (hk (k + 1) (by omega) le_rfl)
    have i1 := inc12 W p hp hR (b + (k + 1)) y z o acc hacc
    rw [show b + (k + 1) - 1 = b + k by omega] at i1
    have rest := ih (fun i h1 h2 => hk i h1 (by omega)) ((acc + 1) % p) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show acc + 1 + k = acc + (k + 1) by omega] at rest
    exact ((TimedLe.single (by rfl) s1).trans (i1.trans rest)).mono (by nlinarith)

omit hp hR in
/-- Before the set bit: pass the empty cells of the block. -/
theorem hu_walk (s x y z : ℕ) (o : List Bool) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → readTapeBit W.B (s + i) = false ∧ readTapeBit W.T (s + i) = false) →
      TimedLe rowM k (rc W 10 (s + k) x y z o) (rc W 10 s x y z o) := by
  intro k
  induction k with
  | zero => intro _; exact TimedLe.refl _ _
  | succ k ih =>
    intro hk
    have h := hk (k + 1) (by omega) le_rfl
    have s1 := r10f W (s + (k + 1)) x y z o h.1 h.2
    rw [show s + (k + 1) - 1 = s + k by omega] at s1
    have t := (TimedLe.single (by rfl) s1).trans (ih (fun i h1 h2 => hk i h1 (by omega)))
    rwa [Nat.add_comm 1] at t

/-- **One block**: from its rightmost cell (state 9) to its left boundary (state 2), adding the digit. -/
theorem block_run (m D : ℕ) (hm : 1 ≤ m) (hB : W.B = Bt m D) (zs : List ℕ) (x : ℕ) (ys : List ℕ)
    (hT : W.T = Tt m (zs ++ x :: ys)) (hd : zs.length < D) (hx : x < m) (acc : ℕ) (hacc : acc < p)
    (z : ℕ) (o : List Bool) :
    TimedLe rowM (m + 2 + m * (p + 2) + 1) (rc W 9 (zs.length * m + m) acc 0 z o)
      (rc W 2 (zs.length * m) ((acc + x) % p) 0 z o) := by
  have hTv : ∀ v, v < m → readTapeBit W.T (1 + zs.length * m + v) = decide (x = v) := by
    intro v hv
    rw [hT, Tt_split, mid_read m zs _ _ v (by rw [oneHot_length]; exact hv), oneHot_getD m x v hv]
  have hBv : ∀ v, v < m → readTapeBit W.B (1 + zs.length * m + v) = decide (v + 1 = m) := by
    intro v hv
    rw [hB]; exact Bt_read m D zs.length v hm hd hv
  have hB0 : readTapeBit W.B (zs.length * m) = true := by
    rw [hB]; exact Bt_read_start m D zs.length hm (by omega)
  have hsw := hs_walk W p hp hR (zs.length * m) hB0 0 z o x
    (fun i h1 h2 => by
      rw [show zs.length * m + i = 1 + zs.length * m + (i - 1) by omega, hBv (i - 1) (by omega)]
      simp only [decide_eq_false_iff_not]; omega) acc hacc
  by_cases hxe : x = m - 1
  · have s1 := r9t W (zs.length * m + m) acc 0 z o (by
      rw [show zs.length * m + m = 1 + zs.length * m + (m - 1) by omega, hTv (m - 1) (by omega)]
      simp only [decide_eq_true_eq]; omega)
    rw [show zs.length * m + m - 1 = zs.length * m + x by omega] at s1
    have hc : x * (p + 2) ≤ m * (p + 2) := Nat.mul_le_mul_right _ (by omega)
    exact ((TimedLe.single (by rfl) s1).trans hsw).mono (by omega)
  · have s1 := r9f W (zs.length * m + m) acc 0 z o (by
      rw [show zs.length * m + m = 1 + zs.length * m + (m - 1) by omega, hTv (m - 1) (by omega)]
      simp only [decide_eq_false_iff_not]; omega)
    rw [show zs.length * m + m - 1 = 1 + zs.length * m + x + (m - 2 - x) by omega] at s1
    have hw := hu_walk W (1 + zs.length * m + x) acc 0 z o (m - 2 - x)
      (fun i h1 h2 => by
        rw [show 1 + zs.length * m + x + i = 1 + zs.length * m + (x + i) by omega, hBv (x + i) (by omega),
          hTv (x + i) (by omega)]
        constructor
        · simp only [decide_eq_false_iff_not]; omega
        · simp only [decide_eq_false_iff_not]; omega)
    have s2 := r10t W (1 + zs.length * m + x) acc 0 z o
      (by rw [hBv x hx]; simp only [decide_eq_false_iff_not]; omega)
      (by rw [hTv x hx]; simp)
    rw [show 1 + zs.length * m + x - 1 = zs.length * m + x by omega] at s2
    have hc : x * (p + 2) ≤ m * (p + 2) := Nat.mul_le_mul_right _ (by omega)
    exact ((TimedLe.single (by rfl) s1).trans (hw.trans ((TimedLe.single (by rfl) s2).trans hsw))).mono
      (by omega)

end Block

/-! ## Phase 2: Horner's rule over all blocks -/

theorem radixList_succ : ∀ (ds : List ℕ) (e : ℕ), radixList ds (e + 1) = 2 * radixList ds e := by
  intro ds
  induction ds with
  | nil => intro e; rfl
  | cons x ds ih =>
    intro e
    simp only [radixList]
    rw [ih (e + 1), pow_succ]
    ring

theorem radixList_cons (x : ℕ) (ds : List ℕ) : radixList (x :: ds) 0 = x + 2 * radixList ds 0 := by
  simp only [radixList, pow_zero, Nat.mul_one]
  rw [radixList_succ]

/-- The cost of one Horner block (doubling, then the block walk). -/
def hornerBlock (m p : ℕ) : ℕ := 1 + (p + 1 + p * (2 * p + 3) + 1) + 1 + (m + 2 + m * (p + 2) + 1)

section Horner
variable (W : RowTapes) (m D p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (hR : ReadsWord W.R (p - 1))
  (hR2 : ReadsWord W.R2 p) (hB : W.B = Bt m D) (hL : W.L = [true]) (ds : List ℕ) (hT : W.T = Tt m ds)
  (hds : ∀ y ∈ ds, y < m) (hD : ds.length = D)
include hm hp hR hR2 hB hL hT hds hD

theorem horner_run (z : ℕ) (o : List Bool) :
    ∀ d, d ≤ D → ∀ acc, acc = radixList (ds.drop d) 0 % p →
      TimedLe rowM (d * hornerBlock m p + 1) (rc W 2 (d * m) acc 0 z o) (rc W 14 0 (radixList ds 0 % p) 0 z o) := by
  intro d
  induction d with
  | zero =>
    intro _ acc hacc
    rw [List.drop_zero] at hacc
    rw [hacc, Nat.zero_mul, Nat.zero_mul, Nat.zero_add]
    exact TimedLe.single (by rfl) (r2d W 0 _ 0 z o (by rw [hL]; rfl))
  | succ d ih =>
    intro hd acc hacc
    have hdl : d < ds.length := by omega
    have hacc' : acc < p := by rw [hacc]; exact Nat.mod_lt _ (by omega)
    have s1 := r2n W ((d + 1) * m) acc 0 z o (by rw [hL]; exact marker_read _ (by nlinarith))
    have dbl := double_run W p hp hR hR2 ((d + 1) * m) z o acc hacc'
    have hsplit : ds = ds.take d ++ ds[d] :: ds.drop (d + 1) := by
      rw [← List.drop_eq_getElem_cons hdl, List.take_append_drop]
    have hzl : (ds.take d).length = d := by rw [List.length_take]; omega
    have blk := block_run W p hp hR m D hm hB (ds.take d) ds[d] (ds.drop (d + 1)) (by rw [← hsplit]; exact hT)
      (by rw [hzl]; omega) (hds _ (List.getElem_mem hdl)) (2 * acc % p) (Nat.mod_lt _ (by omega)) z o
    rw [hzl, show d * m + m = (d + 1) * m by rw [Nat.succ_mul]] at blk
    have hnext : (2 * acc % p + ds[d]) % p = radixList (ds.drop d) 0 % p := by
      rw [List.drop_eq_getElem_cons hdl, radixList_cons, Nat.mod_add_mod, hacc]
      have h := Nat.ModEq.add_right ds[d] (Nat.ModEq.mul_left 2 (Nat.mod_modEq (radixList (ds.drop (d + 1)) 0) p))
      rw [h, Nat.add_comm]
    rw [hnext] at blk
    have rest := ih (by omega) _ rfl
    have hc : acc * (2 * p + 3) ≤ p * (2 * p + 3) := Nat.mul_le_mul_right _ (by omega)
    have hbd : hornerBlock m p = 1 + (p + 1 + p * (2 * p + 3) + 1) + 1 + (m + 2 + m * (p + 2) + 1) := rfl
    exact ((TimedLe.single (by rfl) s1).trans (dbl.trans (blk.trans rest))).mono
      (by rw [show (d + 1) * hornerBlock m p = d * hornerBlock m p + hornerBlock m p from Nat.succ_mul d _]; omega)

end Horner

/-! ## Phase 3: add the residue, append the acceptance bit, rewind -/

section Res
variable (W : RowTapes) (p res : ℕ) (hp : 1 ≤ p) (hR : ReadsWord W.R (p - 1)) (hRS : ReadsWord W.RS res)
include hp hR hRS

theorem res_walk (g y : ℕ) (o : List Bool) (acc : ℕ) (hacc : acc < p) :
    ∀ j, j ≤ res → TimedLe rowM (j * (p + 2)) (rc W 15 g acc y 1 o) (rc W 15 g ((acc + j) % p) y (1 + j) o) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.add_zero, Nat.zero_mul]
    rw [Nat.mod_eq_of_lt hacc]
    exact TimedLe.refl _ _
  | succ j ih =>
    intro hj
    have s1 := r15c W g ((acc + j) % p) y (1 + j) o (hRS.pos (1 + j) (by omega) (by omega))
    have i1 := inc16 W p hp hR g y (1 + j) o ((acc + j) % p) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show acc + j + 1 = acc + (j + 1) by omega, show 1 + j + 1 = 1 + (j + 1) by omega] at i1
    exact ((ih (by omega)).trans ((TimedLe.single (by rfl) s1).trans i1)).mono (by rw [Nat.succ_mul]; omega)

omit hRS in
theorem accept_bit (v : ℕ) (hv : v < p) : (!readTapeBit W.R v) = decide (v = 0) := by
  rw [hR v]
  by_cases h : v = 0
  · subst h; simp
  · have h1 : 1 ≤ v := by omega
    have h2 : v ≤ p - 1 := by omega
    simp [h, h1, h2]

/-- **Phase 3**: from state 14 (group at `0`, `R = acc`) to the halt, the acceptance bit appended. -/
theorem phase3 (acc : ℕ) (hacc : acc < p) (o : List Bool) :
    TimedLe rowM (1 + res * (p + 2) + 1 + res + 1 + 1 + p + 1) (rc W 14 0 acc 0 0 o)
      (rc W 21 0 0 0 0 (o ++ [decide ((acc + res) % p = 0)])) := by
  have s0 := r14 W 0 acc 0 0 o
  have w := res_walk W p res hp hR hRS 0 0 o acc hacc res le_rfl
  have s1 := r15e W 0 ((acc + res) % p) 0 (1 + res) o (hRS.past (1 + res) (by omega))
  rw [show 1 + res - 1 = res by omega] at s1
  have w2 := walkRS W 0 ((acc + res) % p) 0 o res (fun i h1 h2 => hRS.pos i h1 h2)
  have s2 := r18e W 0 ((acc + res) % p) 0 0 o hRS.zero
  have s3 := r19 W 0 ((acc + res) % p) 0 0 o
  rw [accept_bit W p hp hR _ (Nat.mod_lt _ (by omega))] at s3
  have w3 := walkR W 20 (by rfl) 0 0 0 (o ++ [decide ((acc + res) % p = 0)]) (fun x h => r20c W 0 x 0 0 _ h)
    ((acc + res) % p) (R_all W p hR _ (by have := Nat.mod_lt (acc + res) (show p > 0 by omega); omega))
  have s4 := r20e W 0 0 0 0 (o ++ [decide ((acc + res) % p = 0)]) hR.zero
  have hle : (acc + res) % p ≤ p := (Nat.mod_lt _ (by omega)).le
  exact ((TimedLe.single (by rfl) s0).trans (w.trans ((TimedLe.single (by rfl) s1).trans (w2.trans
    ((TimedLe.single (by rfl) s2).trans ((TimedLe.single (by rfl) s3).trans (w3.trans
      (TimedLe.single (by rfl) s4)))))))).mono (by omega)

end Res

/-! ## The whole row -/

/-- The step budget of one row. -/
def rowCost (m D p res : ℕ) : ℕ :=
  D * m + 2 + (D * hornerBlock m p + 1) + (1 + res * (p + 2) + 1 + res + 1 + 1 + p + 1)

/-- The row configuration's banks. -/
def rowH (o : List Bool) : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, o.length]
def rowA (W : RowTapes) (o : List Bool) : Fin 8 → List Bool := ![W.L, W.T, W.B, W.KW, W.R, W.R2, W.RS, o]

/-- **One code's row, exactly.** -/
theorem row_run (m D p res : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (W : RowTapes) (hL : W.L = [true]) (ds : List ℕ)
    (hds : ∀ y ∈ ds, y < m) (hD : ds.length = D) (hT : W.T = Tt m ds) (hB : W.B = Bt m D)
    (hK : ReadsWord W.KW (D * m)) (hR : ReadsWord W.R (p - 1)) (hR2 : ReadsWord W.R2 p)
    (hRS : ReadsWord W.RS res) (o : List Bool) :
    Step rowM (rowCost m D p res) (rowH o) (rowA W o)
      (rowH (o ++ (blocksOf m ds ++ [decide ((res + radixList ds 0) % p = 0)])))
      (rowA W (o ++ (blocksOf m ds ++ [decide ((res + radixList ds 0) % p = 0)]))) := by
  have t1 := phase1 W (blocksOf m ds) hT (D * m) hK (by rw [blocksOf_length, hD]) 0 0 0 o
  have t2 := horner_run W m D p hm hp hR hR2 hB hL ds hT hds hD 0 (o ++ blocksOf m ds) D le_rfl _ rfl
  rw [List.drop_of_length_le (by omega)] at t2
  have t2' : TimedLe rowM (D * hornerBlock m p + 1) (rc W 2 (D * m) 0 0 0 (o ++ blocksOf m ds))
      (rc W 14 0 (radixList ds 0 % p) 0 0 (o ++ blocksOf m ds)) := by
    have h0 : radixList [] 0 % p = 0 := Nat.zero_mod p
    rw [h0] at t2
    exact t2
  have t3 := phase3 W p res hp hR hRS (radixList ds 0 % p) (Nat.mod_lt _ (by omega)) (o ++ blocksOf m ds)
  rw [Nat.mod_add_mod, Nat.add_comm (radixList ds 0), List.append_assoc] at t3
  exact ((t1.trans (t2'.trans t3)).mono (by unfold rowCost; omega)).toStep (by rfl)

end NearCubicWires.PacketsCombine.Tab

