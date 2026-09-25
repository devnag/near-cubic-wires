import Proof.Packets.PacketsCombineTabOdo

/-! # P2 (iii) table writer, part 3: the row machine (one code's row of the THR selection table)

Consumer: the THR selection-table writer (`ThrMeta`'s tape 15, `Proof/Packets/PacketsCombineThrLocal.lean`): per code `c`
(ascending) the one-hot blocks of its digit tuple, then the acceptance bit
`modularTupleAccepts prime residue 2` = `decide ((res + radixList ds 0) % p = 0)` (`rowOf`,
`PacketsCombineTabMeaning`). Paper: A.13.7 (`paper.tex:3113-3142`), the tuples are internal preprocessing
charged in `T_prep` (`paper.tex:1197-1200`); budget class source-polynomial (a fixed polynomial of
`m, D, p, res`).

`rowM : Machine 8 22`, tapes: `0` the marker `[true]`, `1` the tuple tape `Tt m ds`, `2` the block-end tape
`Bt m D` (these three are the odometer's), `3` a word reading as `word (D*m)` (the copy bound), `4` the
residue register `R` (reads as `word (p-1)`; value = head position), `5` the doubling register (reads as
`word p`), `6` a word reading as `word res`, `7` the output (appended at its end).
Phases: copy the `D*m` tuple cells to the output (states `0,1`); walk back over the blocks, most significant
first, computing `radixList ds 0 mod p` by Horner's rule (states `2..13`: at each block `R := 2R mod p` through
the doubling register, then `+ digit` by counting the cells left of the set bit); add `res` (states
`14..17`); append `R = 0` and rewind (states `18..20`). No division, no binary arithmetic: every register
operation is a head walk. This module: the machine, its configurations, every transition, the register
walks.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

/-! ## The machine -/

/-- One action: write `w` on the output (tape 7), move the group `0..3` by `g`, `R` by `r`, the doubling
register by `r2`, the residue word by `s`, the output by `o`. -/
def ract (q : Fin 22) (g r r2 s o : HeadMove) (w : Option Bool) : Action 8 22 :=
  ⟨q, fun i => if i.val = 7 then w else none,
    fun i => if i.val < 4 then g else if i.val = 4 then r else if i.val = 5 then r2 else if i.val = 6 then s else o⟩

def rowM : Machine 8 22 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 21
  rule := fun q sc =>
    if q.val = 0 then some (ract 1 .right .stay .stay .stay .stay none)
    else if q.val = 1 then some (if sc 3 then ract 1 .right .stay .stay .stay .right (some (sc 1))
      else ract 2 .left .stay .stay .stay .stay none)
    else if q.val = 2 then some (if sc 0 then ract 14 .stay .stay .stay .stay .stay none
      else ract 3 .stay .stay .stay .stay .stay none)
    else if q.val = 3 then some (if sc 4 then ract 3 .stay .left .right .stay .stay none
      else ract 4 .stay .stay .stay .stay .stay none)
    else if q.val = 4 then some (if sc 5 then ract 5 .stay .right .left .stay .stay none
      else ract 9 .stay .stay .stay .stay .stay none)
    else if q.val = 5 then some (if sc 4 then ract 7 .stay .right .stay .stay .stay none
      else ract 6 .stay .left .stay .stay .stay none)
    else if q.val = 6 then some (if sc 4 then ract 6 .stay .left .stay .stay .stay none
      else ract 7 .stay .right .stay .stay .stay none)
    else if q.val = 7 then some (if sc 4 then ract 4 .stay .stay .stay .stay .stay none
      else ract 8 .stay .left .stay .stay .stay none)
    else if q.val = 8 then some (if sc 4 then ract 8 .stay .left .stay .stay .stay none
      else ract 4 .stay .stay .stay .stay .stay none)
    else if q.val = 9 then some (if sc 1 then ract 11 .left .stay .stay .stay .stay none
      else ract 10 .left .stay .stay .stay .stay none)
    else if q.val = 10 then some (if sc 2 then ract 2 .stay .stay .stay .stay .stay none
      else if sc 1 then ract 11 .left .stay .stay .stay .stay none
      else ract 10 .left .stay .stay .stay .stay none)
    else if q.val = 11 then some (if sc 2 then ract 2 .stay .stay .stay .stay .stay none
      else ract 12 .stay .right .stay .stay .stay none)
    else if q.val = 12 then some (if sc 4 then ract 11 .left .stay .stay .stay .stay none
      else ract 13 .stay .left .stay .stay .stay none)
    else if q.val = 13 then some (if sc 4 then ract 13 .stay .left .stay .stay .stay none
      else ract 11 .left .stay .stay .stay .stay none)
    else if q.val = 14 then some (ract 15 .stay .stay .stay .right .stay none)
    else if q.val = 15 then some (if sc 6 then ract 16 .stay .right .stay .stay .stay none
      else ract 18 .stay .stay .stay .left .stay none)
    else if q.val = 16 then some (if sc 4 then ract 15 .stay .stay .stay .right .stay none
      else ract 17 .stay .left .stay .stay .stay none)
    else if q.val = 17 then some (if sc 4 then ract 17 .stay .left .stay .stay .stay none
      else ract 15 .stay .stay .stay .right .stay none)
    else if q.val = 18 then some (if sc 6 then ract 18 .stay .stay .stay .left .stay none
      else ract 19 .stay .stay .stay .stay .stay none)
    else if q.val = 19 then some (ract 20 .stay .stay .stay .stay .right (some (!sc 4)))
    else if q.val = 20 then some (if sc 4 then ract 20 .stay .left .stay .stay .stay none
      else ract 21 .stay .stay .stay .stay .stay none)
    else none

/-- The seven tapes the row machine only reads. -/
structure RowTapes where
  L : List Bool
  T : List Bool
  B : List Bool
  KW : List Bool
  R : List Bool
  R2 : List Bool
  RS : List Bool

/-- The row configuration: group head `g` (tapes `0..3`), `R` at `x`, doubling register at `y`, residue
word at `z`, output head at its end. -/
def rc (W : RowTapes) (q : Fin 22) (g x y z : ℕ) (out : List Bool) : Configuration 8 22 :=
  ⟨q, ![g, g, g, g, x, y, z, out.length], ![W.L, W.T, W.B, W.KW, W.R, W.R2, W.RS, out]⟩

@[simp] theorem rc_control (W : RowTapes) (q : Fin 22) (g x y z : ℕ) (out : List Bool) :
    (rc W q g x y z out).control = q := rfl

theorem rc_apply (W : RowTapes) (q q' : Fin 22) (g x y z : ℕ) (out : List Bool) (mg mr mr2 ms : HeadMove) :
    applyAction (rc W q g x y z out) (ract q' mg mr mr2 ms .stay none) =
      rc W q' (mg.apply g) (mr.apply x) (mr2.apply y) (ms.apply z) out := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem rc_apply_out (W : RowTapes) (q q' : Fin 22) (g x y z : ℕ) (out : List Bool) (mg : HeadMove) (b : Bool) :
    applyAction (rc W q g x y z out) (ract q' mg .stay .stay .stay .right (some b)) =
      rc W q' (mg.apply g) x y z (out ++ [b]) := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, rc, ract, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, rc, ract]
    exact Streaming.write_append out b

theorem rc_scan (W : RowTapes) (q : Fin 22) (g x y z : ℕ) (out : List Bool) :
    (rc W q g x y z out).scanned = ![readTapeBit W.L g, readTapeBit W.T g, readTapeBit W.B g,
      readTapeBit W.KW g, readTapeBit W.R x, readTapeBit W.R2 y, readTapeBit W.RS z,
      readTapeBit out out.length] := by
  funext i; fin_cases i <;> rfl

/-! ## Transitions -/

section Trans
variable (W : RowTapes) (g x y z : ℕ) (o : List Bool)

theorem r0 : LocalBitMultitape.step rowM (rc W 0 g x y z o) = some (rc W 1 (g + 1) x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, rc_apply, HeadMove.apply]

theorem r1c (h : readTapeBit W.KW g = true) :
    LocalBitMultitape.step rowM (rc W 1 g x y z o) = some (rc W 1 (g + 1) x y z (o ++ [readTapeBit W.T g])) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply_out, HeadMove.apply]

theorem r1e (h : readTapeBit W.KW g = false) :
    LocalBitMultitape.step rowM (rc W 1 g x y z o) = some (rc W 2 (g - 1) x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r2d (h : readTapeBit W.L g = true) :
    LocalBitMultitape.step rowM (rc W 2 g x y z o) = some (rc W 14 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r2n (h : readTapeBit W.L g = false) :
    LocalBitMultitape.step rowM (rc W 2 g x y z o) = some (rc W 3 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r3c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 3 g x y z o) = some (rc W 3 g (x - 1) (y + 1) z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r3e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 3 g x y z o) = some (rc W 4 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r4c (h : readTapeBit W.R2 y = true) :
    LocalBitMultitape.step rowM (rc W 4 g x y z o) = some (rc W 5 g (x + 1) (y - 1) z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r4e (h : readTapeBit W.R2 y = false) :
    LocalBitMultitape.step rowM (rc W 4 g x y z o) = some (rc W 9 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r5c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 5 g x y z o) = some (rc W 7 g (x + 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r5e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 5 g x y z o) = some (rc W 6 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r6c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 6 g x y z o) = some (rc W 6 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r6e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 6 g x y z o) = some (rc W 7 g (x + 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r7c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 7 g x y z o) = some (rc W 4 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r7e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 7 g x y z o) = some (rc W 8 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r8c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 8 g x y z o) = some (rc W 8 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r8e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 8 g x y z o) = some (rc W 4 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r9t (h : readTapeBit W.T g = true) :
    LocalBitMultitape.step rowM (rc W 9 g x y z o) = some (rc W 11 (g - 1) x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r9f (h : readTapeBit W.T g = false) :
    LocalBitMultitape.step rowM (rc W 9 g x y z o) = some (rc W 10 (g - 1) x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r10t (hB : readTapeBit W.B g = false) (h : readTapeBit W.T g = true) :
    LocalBitMultitape.step rowM (rc W 10 g x y z o) = some (rc W 11 (g - 1) x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, hB, h, rc_apply, HeadMove.apply]

theorem r10f (hB : readTapeBit W.B g = false) (h : readTapeBit W.T g = false) :
    LocalBitMultitape.step rowM (rc W 10 g x y z o) = some (rc W 10 (g - 1) x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, hB, h, rc_apply, HeadMove.apply]

theorem r11b (h : readTapeBit W.B g = true) :
    LocalBitMultitape.step rowM (rc W 11 g x y z o) = some (rc W 2 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r11n (h : readTapeBit W.B g = false) :
    LocalBitMultitape.step rowM (rc W 11 g x y z o) = some (rc W 12 g (x + 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r12c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 12 g x y z o) = some (rc W 11 (g - 1) x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r12e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 12 g x y z o) = some (rc W 13 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r13c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 13 g x y z o) = some (rc W 13 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r13e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 13 g x y z o) = some (rc W 11 (g - 1) x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r14 : LocalBitMultitape.step rowM (rc W 14 g x y z o) = some (rc W 15 g x y (z + 1) o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, rc_apply, HeadMove.apply]

theorem r15c (h : readTapeBit W.RS z = true) :
    LocalBitMultitape.step rowM (rc W 15 g x y z o) = some (rc W 16 g (x + 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r15e (h : readTapeBit W.RS z = false) :
    LocalBitMultitape.step rowM (rc W 15 g x y z o) = some (rc W 18 g x y (z - 1) o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r16c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 16 g x y z o) = some (rc W 15 g x y (z + 1) o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r16e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 16 g x y z o) = some (rc W 17 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r17c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 17 g x y z o) = some (rc W 17 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r17e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 17 g x y z o) = some (rc W 15 g x y (z + 1) o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r18c (h : readTapeBit W.RS z = true) :
    LocalBitMultitape.step rowM (rc W 18 g x y z o) = some (rc W 18 g x y (z - 1) o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r18e (h : readTapeBit W.RS z = false) :
    LocalBitMultitape.step rowM (rc W 18 g x y z o) = some (rc W 19 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r19 : LocalBitMultitape.step rowM (rc W 19 g x y z o) = some (rc W 20 g x y z (o ++ [!readTapeBit W.R x])) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, rc_apply_out, HeadMove.apply]

theorem r20c (h : readTapeBit W.R x = true) :
    LocalBitMultitape.step rowM (rc W 20 g x y z o) = some (rc W 20 g (x - 1) y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

theorem r20e (h : readTapeBit W.R x = false) :
    LocalBitMultitape.step rowM (rc W 20 g x y z o) = some (rc W 21 g x y z o) := by
  simp [LocalBitMultitape.step, rowM, rc_scan, h, rc_apply, HeadMove.apply]

end Trans

/-! ## Registers reading as unary words -/

/-- A tape that reads as `CompareMachine.word X`: `false` at `0`, `true` on `1..X`, `false` beyond. -/
def ReadsWord (A : List Bool) (X : ℕ) : Prop := ∀ k, readTapeBit A k = decide (1 ≤ k ∧ k ≤ X)

theorem ReadsWord.pos {A : List Bool} {X : ℕ} (h : ReadsWord A X) (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ X) :
    readTapeBit A k = true := by rw [h k]; simp only [decide_eq_true_eq]; omega

theorem ReadsWord.zero {A : List Bool} {X : ℕ} (h : ReadsWord A X) : readTapeBit A 0 = false := by
  rw [h 0]; simp

theorem ReadsWord.past {A : List Bool} {X : ℕ} (h : ReadsWord A X) (k : ℕ) (hk : X < k) :
    readTapeBit A k = false := by rw [h k]; simp only [decide_eq_false_iff_not]; omega

theorem readsWord_word (X : ℕ) : ReadsWord (CompareMachine.word X) X := word_read X

/-! ## Left walks on one register -/

section Walks
variable (W : RowTapes)

/-- A left walk of `R` in a fixed state `s` while it reads `true`. -/
theorem walkR (s : Fin 22) (hs : rowM.halted s = false) (g y z : ℕ) (o : List Bool)
    (hstep : ∀ x, readTapeBit W.R x = true →
      LocalBitMultitape.step rowM (rc W s g x y z o) = some (rc W s g (x - 1) y z o)) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → readTapeBit W.R i = true) →
      TimedLe rowM k (rc W s g k y z o) (rc W s g 0 y z o) := by
  intro k
  induction k with
  | zero => intro _; exact TimedLe.refl _ _
  | succ k ih =>
    intro hk
    have h1 := hstep (k + 1) (hk (k + 1) (by omega) le_rfl)
    rw [Nat.add_sub_cancel] at h1
    have t := (TimedLe.single hs h1).trans (ih (fun i h1 h2 => hk i h1 (by omega)))
    rwa [Nat.add_comm 1] at t

/-- The residue word's rewind (state 18). -/
theorem walkRS (g x y : ℕ) (o : List Bool) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → readTapeBit W.RS i = true) →
      TimedLe rowM k (rc W 18 g x y k o) (rc W 18 g x y 0 o) := by
  intro k
  induction k with
  | zero => intro _; exact TimedLe.refl _ _
  | succ k ih =>
    intro hk
    have h1 := r18c W g x y (k + 1) o (hk (k + 1) (by omega) le_rfl)
    rw [Nat.add_sub_cancel] at h1
    have t := (TimedLe.single (by rfl) h1).trans (ih (fun i h1 h2 => hk i h1 (by omega)))
    rwa [Nat.add_comm 1] at t

/-- The first doubling walk (state 3): move `R`'s value onto the doubling register. -/
theorem walkD1 (g z : ℕ) (o : List Bool) :
    ∀ k y, (∀ i, 1 ≤ i → i ≤ k → readTapeBit W.R i = true) →
      TimedLe rowM k (rc W 3 g k y z o) (rc W 3 g 0 (y + k) z o) := by
  intro k
  induction k with
  | zero => intro y _; exact TimedLe.refl _ _
  | succ k ih =>
    intro y hk
    have h1 := r3c W g (k + 1) y z o (hk (k + 1) (by omega) le_rfl)
    rw [Nat.add_sub_cancel] at h1
    have t := (TimedLe.single (by rfl) h1).trans (ih (y + 1) (fun i h1 h2 => hk i h1 (by omega)))
    rw [show y + 1 + k = y + (k + 1) by omega, Nat.add_comm 1] at t
    exact t

end Walks

/-! ## One modular increment of `R` -/

theorem R_all (W : RowTapes) (p : ℕ) (hR : ReadsWord W.R (p - 1)) (k : ℕ) (hk : k ≤ p - 1) :
    ∀ i, 1 ≤ i → i ≤ k → readTapeBit W.R i = true :=
  fun i h1 h2 => hR.pos i h1 (by omega)

section Inc
variable (W : RowTapes) (p : ℕ) (hp : 1 ≤ p) (hR : ReadsWord W.R (p - 1))
include hp hR

/-- Doubling, part 2, first increment: from state 5 with `R` moved to `x+1`, reach state 7 with `R` at
`(x+1) % p + 1`. -/
theorem inc5 (g y z : ℕ) (o : List Bool) (x : ℕ) (hx : x < p) :
    TimedLe rowM (p + 1) (rc W 5 g (x + 1) y z o) (rc W 7 g ((x + 1) % p + 1) y z o) := by
  by_cases hlt : x + 1 < p
  · rw [Nat.mod_eq_of_lt hlt]
    exact (TimedLe.single (by rfl) (r5c W g (x + 1) y z o (hR.pos (x + 1) (by omega) (by omega)))).mono (by omega)
  · have hxp : x + 1 = p := by omega
    rw [hxp, Nat.mod_self]
    have s1 := r5e W g p y z o (hR.past p (by omega))
    have w := walkR W 6 (by rfl) g y z o (fun x h => r6c W g x y z o h) (p - 1) (R_all W p hR (p - 1) le_rfl)
    have s2 := r6e W g 0 y z o hR.zero
    exact ((TimedLe.single (by rfl) s1).trans (w.trans (TimedLe.single (by rfl) s2))).mono (by omega)

/-- Doubling, part 2, second increment: from state 7 with `R` at `x+1`, reach state 4 at `(x+1) % p`. -/
theorem inc7 (g y z : ℕ) (o : List Bool) (x : ℕ) (hx : x < p) :
    TimedLe rowM (p + 1) (rc W 7 g (x + 1) y z o) (rc W 4 g ((x + 1) % p) y z o) := by
  by_cases hlt : x + 1 < p
  · rw [Nat.mod_eq_of_lt hlt]
    exact (TimedLe.single (by rfl) (r7c W g (x + 1) y z o (hR.pos (x + 1) (by omega) (by omega)))).mono (by omega)
  · have hxp : x + 1 = p := by omega
    rw [hxp, Nat.mod_self]
    have s1 := r7e W g p y z o (hR.past p (by omega))
    have w := walkR W 8 (by rfl) g y z o (fun x h => r8c W g x y z o h) (p - 1) (R_all W p hR (p - 1) le_rfl)
    have s2 := r8e W g 0 y z o hR.zero
    exact ((TimedLe.single (by rfl) s1).trans (w.trans (TimedLe.single (by rfl) s2))).mono (by omega)

/-- The in-block increment (state 12): `R` at `x+1`; reach state 11, group one cell left, `R` at `(x+1) % p`. -/
theorem inc12 (g y z : ℕ) (o : List Bool) (x : ℕ) (hx : x < p) :
    TimedLe rowM (p + 1) (rc W 12 g (x + 1) y z o) (rc W 11 (g - 1) ((x + 1) % p) y z o) := by
  by_cases hlt : x + 1 < p
  · rw [Nat.mod_eq_of_lt hlt]
    exact (TimedLe.single (by rfl) (r12c W g (x + 1) y z o (hR.pos (x + 1) (by omega) (by omega)))).mono (by omega)
  · have hxp : x + 1 = p := by omega
    rw [hxp, Nat.mod_self]
    have s1 := r12e W g p y z o (hR.past p (by omega))
    have w := walkR W 13 (by rfl) g y z o (fun x h => r13c W g x y z o h) (p - 1) (R_all W p hR (p - 1) le_rfl)
    have s2 := r13e W g 0 y z o hR.zero
    exact ((TimedLe.single (by rfl) s1).trans (w.trans (TimedLe.single (by rfl) s2))).mono (by omega)

/-- The residue increment (state 16): `R` at `x+1`; reach state 15, residue word one cell right. -/
theorem inc16 (g y z : ℕ) (o : List Bool) (x : ℕ) (hx : x < p) :
    TimedLe rowM (p + 1) (rc W 16 g (x + 1) y z o) (rc W 15 g ((x + 1) % p) y (z + 1) o) := by
  by_cases hlt : x + 1 < p
  · rw [Nat.mod_eq_of_lt hlt]
    exact (TimedLe.single (by rfl) (r16c W g (x + 1) y z o (hR.pos (x + 1) (by omega) (by omega)))).mono (by omega)
  · have hxp : x + 1 = p := by omega
    rw [hxp, Nat.mod_self]
    have s1 := r16e W g p y z o (hR.past p (by omega))
    have w := walkR W 17 (by rfl) g y z o (fun x h => r17c W g x y z o h) (p - 1) (R_all W p hR (p - 1) le_rfl)
    have s2 := r17e W g 0 y z o hR.zero
    exact ((TimedLe.single (by rfl) s1).trans (w.trans (TimedLe.single (by rfl) s2))).mono (by omega)

end Inc

/-! ## Doubling `R` modulo `p` -/

section Double
variable (W : RowTapes) (p : ℕ) (hp : 1 ≤ p) (hR : ReadsWord W.R (p - 1)) (hR2 : ReadsWord W.R2 p)
include hp hR hR2

/-- The second doubling walk (state 4): each unit of the doubling register adds `2` to `R` modulo `p`. -/
theorem walkD2 (g z : ℕ) (o : List Bool) :
    ∀ k x, k ≤ p → x < p → TimedLe rowM (k * (2 * p + 3)) (rc W 4 g x k z o) (rc W 4 g ((x + 2 * k) % p) 0 z o) := by
  intro k
  induction k with
  | zero =>
    intro x _ hx
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mul]
    rw [Nat.mod_eq_of_lt hx]
    exact TimedLe.refl _ _
  | succ k ih =>
    intro x hk hx
    have s1 := r4c W g x (k + 1) z o (hR2.pos (k + 1) (by omega) hk)
    rw [Nat.add_sub_cancel] at s1
    have i1 := inc5 W p hp hR g k z o x hx
    have hy : (x + 1) % p < p := Nat.mod_lt _ (by omega)
    have i2 := inc7 W p hp hR g k z o ((x + 1) % p) hy
    have rest := ih (((x + 1) % p + 1) % p) (by omega) (Nat.mod_lt _ (by omega))
    have he : (((x + 1) % p + 1) % p + 2 * k) % p = (x + 2 * (k + 1)) % p := by
      rw [Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]
      congr 1
      omega
    rw [he] at rest
    exact ((TimedLe.single (by rfl) s1).trans (i1.trans (i2.trans rest))).mono (by nlinarith)

/-- **Doubling**: from state 3 with `R = x < p` (doubling register at `0`) to state 9 with `R = 2x mod p`. -/
theorem double_run (g z : ℕ) (o : List Bool) (x : ℕ) (hx : x < p) :
    TimedLe rowM (x + 1 + x * (2 * p + 3) + 1) (rc W 3 g x 0 z o) (rc W 9 g (2 * x % p) 0 z o) := by
  have w1 := walkD1 W g z o x 0 (R_all W p hR x (by omega))
  rw [Nat.zero_add] at w1
  have s1 := r3e W g 0 x z o hR.zero
  have w2 := walkD2 W p hp hR hR2 g z o x 0 (by omega) (by omega)
  rw [Nat.zero_add] at w2
  have s2 := r4e W g (2 * x % p) 0 z o hR2.zero
  exact (w1.trans ((TimedLe.single (by rfl) s1).trans (w2.trans (TimedLe.single (by rfl) s2)))).mono (by omega)

end Double

end NearCubicWires.PacketsCombine.Tab

