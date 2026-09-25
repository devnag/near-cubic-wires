import Proof.Packets.PacketsKeysThrState

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsKeys.ThrProg
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys.RM
open NearCubicWires.RepairRepresentation
noncomputable section

/-! ## Streams on the circuit tapes -/

/-- The marks of a stream. -/
def mks (pay : List Bool) : ℕ → Bool := sf (List.replicate pay.length true)

/-- Circuit `c`'s stream holds `pay` at cursor `q` (both tapes). -/
def strm (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q : ℕ) : Fin 8 → TS :=
  Function.update (Function.update base (cs c) (.cells (sf pay) q)) (cm c) (.cells (mks pay) q)

theorem cs_ne_cm (c : Fin 4) : cs c ≠ cm c := by
  intro e; have := congrArg Fin.val e; simp only [cs, cm] at this; omega

theorem ocs_ocm (c : Fin 4) : (ocs c).val ≠ (ocm c).val := by simp [ocs, ocm]

theorem strm_cs (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q : ℕ) :
    strm base c pay q (cs c) = .cells (sf pay) q := by
  simp [strm, Function.update_of_ne (cs_ne_cm c)]

theorem strm_cm (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q : ℕ) :
    strm base c pay q (cm c) = .cells (mks pay) q := by
  simp [strm]

theorem strm_ms (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q q' : ℕ) :
    Function.update (Function.update (strm base c pay q) (cs c) (.cells (sf pay) q')) (cm c) (.cells (mks pay) q') =
      strm base c pay q' := by
  funext i
  simp only [strm, Function.update_apply]
  split_ifs <;> simp_all [cs_ne_cm c]

theorem strm_sm (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q q' : ℕ) :
    Function.update (Function.update (strm base c pay q) (cm c) (.cells (mks pay) q')) (cs c) (.cells (sf pay) q') =
      strm base c pay q' := by
  have h1 := cs_ne_cm c
  have h2 := (cs_ne_cm c).symm
  funext i
  simp only [strm, Function.update_apply]
  split_ifs <;> simp_all

theorem oset2 (z : TZ) (c : Fin 4) (u v : TS) :
    Function.update (Function.update (otv z) (ocs c) u) (ocm c) v =
      otv { z with cc := Function.update (Function.update z.cc (cs c) u) (cm c) v } := by
  rw [oset_cs, oset_cm]

theorem oset2' (z : TZ) (c : Fin 4) (u v : TS) :
    Function.update (Function.update (otv z) (ocm c) u) (ocs c) v =
      otv { z with cc := Function.update (Function.update z.cc (cm c) u) (cs c) v } := by
  rw [oset_cm, oset_cs]

theorem fixR {s : St 24 29} {z' : TZ} (h1 : s.rl = z'.rl) (h2 : s.fl = z'.fl) (h3 : s.rg = rgv z')
    (h4 : s.ot = otv z') : roles s = roles (toSt z') := congrArg roles (st_eq h1 h2 h3 h4)

/-! ## Reading numbers on circuit `c` -/

section Read
variable {W : ℕ} (z : TZ) (hr : z.rl = .ruler) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool)
include hr

omit hr in
theorem hS_of (q v : ℕ) (pre post : List Bool) (hpay : pay = pre ++ natWord v ++ post) (hq : q = pre.length + 1) :
    ∀ i, i < (natWord v).length → sf pay (q + i) = (natWord v).getD i false := by
  intro i hi
  rw [hpay, hq]
  rw [show pre.length + 1 + i = pre.length + i + 1 by omega, sf_succ, List.append_assoc,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, List.getD_append _ _ _ _ hi]

/-- `A := natWord` from circuit `c`. -/
theorem rnA (q v : ℕ) (hz : z.cc = strm base c pay q) (hW : natBitLength v ≤ W)
    (hS : ∀ i, i < (natWord v).length → sf pay (q + i) = (natWord v).getD i false) :
    LRuns W (mReadNat (ocs c) (ocm c) rA) (3 * W + 5) (roles (toSt z))
      (roles (toSt { z with cc := strm base c pay (q + (natWord v).length), A := v })) := by
  have h := readNat_run (W := W) (toSt z) hr (ocs c) (ocm c) (ocs_ocm c) rA q v (sf pay) (mks pay) hW hS
    (by show otv z (ocs c) = _; rw [get_cs, hz, strm_cs]) (by show otv z (ocm c) = _; rw [get_cm, hz, strm_cm])
  refine h.congr_out (fixR rfl rfl (set_A z v) ?_)
  show Function.update (Function.update (otv z) (ocs c) _) (ocm c) _ = _
  rw [oset2, hz, strm_ms]
  rfl

/-- `X := natWord` from circuit `c`. -/
theorem rnX (q v : ℕ) (hz : z.cc = strm base c pay q) (hW : natBitLength v ≤ W)
    (hS : ∀ i, i < (natWord v).length → sf pay (q + i) = (natWord v).getD i false) :
    LRuns W (mReadNat (ocs c) (ocm c) rX) (3 * W + 5) (roles (toSt z))
      (roles (toSt { z with cc := strm base c pay (q + (natWord v).length), X := v })) := by
  have h := readNat_run (W := W) (toSt z) hr (ocs c) (ocm c) (ocs_ocm c) rX q v (sf pay) (mks pay) hW hS
    (by show otv z (ocs c) = _; rw [get_cs, hz, strm_cs]) (by show otv z (ocm c) = _; rw [get_cm, hz, strm_cm])
  refine h.congr_out (fixR rfl rfl (set_X z v) ?_)
  show Function.update (Function.update (otv z) (ocs c) _) (ocm c) _ = _
  rw [oset2, hz, strm_ms]
  rfl

omit hr in
/-- `flag := bit` from circuit `c` (the sign of the next signed number). -/
theorem rbit (q : ℕ) (hz : z.cc = strm base c pay q) :
    LRuns W (mBit (NR := 24) (ocm c) (ocs c)) 1 (roles (toSt z))
      (roles (toSt { z with cc := strm base c pay (q + 1), fl := sf pay q })) := by
  have h := bit_run (W := W) (toSt z) (ocm c) (ocs c) (Ne.symm (ocs_ocm c)) (sf pay) (mks pay) q
    (by show otv z (ocs c) = _; rw [get_cs, hz, strm_cs]) (by show otv z (ocm c) = _; rw [get_cm, hz, strm_cm])
  refine h.congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (otv z) (ocm c) _) (ocs c) _ = _
  rw [oset2', hz, strm_sm]
  rfl

end Read

/-! ## Register steps on `TZ` -/

section Regs
variable {W : ℕ} (z : TZ) (hr : z.rl = .ruler)
include hr

theorem zX : LRuns W (mZero (NO := 29) rX) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with X := 0, fl := false })) :=
  (zero_run (W := W) (toSt z) hr rX).congr_out (fixR (z' := { z with X := 0, fl := false }) rfl rfl (set_X z 0) rfl)

theorem zA : LRuns W (mZero (NO := 29) rA) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with A := 0, fl := false })) :=
  (zero_run (W := W) (toSt z) hr rA).congr_out (fixR (z' := { z with A := 0, fl := false }) rfl rfl (set_A z 0) rfl)

theorem decI (h : z.I < 2 ^ W) (h1 : 1 ≤ z.I) :
    LRuns W (mDec (NO := 29) rI) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with I := z.I - 1, fl := false })) :=
  (dec_run (W := W) (toSt z) hr rI h h1).congr_out
    (fixR (z' := { z with I := z.I - 1, fl := false }) rfl rfl (set_I z _) rfl)

theorem decK (h : z.K < 2 ^ W) (h1 : 1 ≤ z.K) :
    LRuns W (mDec (NO := 29) rK) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with K := z.K - 1, fl := false })) :=
  (dec_run (W := W) (toSt z) hr rK h h1).congr_out
    (fixR (z' := { z with K := z.K - 1, fl := false }) rfl rfl (set_K z _) rfl)

theorem posI (h : z.I < 2 ^ W) :
    LRuns W (mPos (NO := 29) rI) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with fl := decide (0 < z.I) })) :=
  (pos_run (W := W) (toSt z) hr rI h).congr_out (fixR (z' := { z with fl := decide (0 < z.I) }) rfl rfl rfl rfl)

theorem posK (h : z.K < 2 ^ W) :
    LRuns W (mPos (NO := 29) rK) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with fl := decide (0 < z.K) })) :=
  (pos_run (W := W) (toSt z) hr rK h).congr_out (fixR (z' := { z with fl := decide (0 < z.K) }) rfl rfl rfl rfl)

theorem cpyIA (h : z.A < 2 ^ W) :
    LRuns W (mCpy (NO := 29) rI rA) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with I := z.A, fl := false })) :=
  (cpy_run (W := W) (toSt z) hr rI rA (by decide) h).congr_out
    (fixR (z' := { z with I := z.A, fl := false }) rfl rfl (set_I z _) rfl)

theorem incI (h : z.I + 1 < 2 ^ W) :
    LRuns W (mInc (NO := 29) rI) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with I := z.I + 1, fl := false })) :=
  (inc_run (W := W) (toSt z) hr rI h).congr_out
    (fixR (z' := { z with I := z.I + 1, fl := false }) rfl rfl (set_I z _) rfl)

theorem cpyKS (c : Fin 4) (h : z.S c < 2 ^ W) :
    LRuns W (mCpy (NO := 29) rK (rS c)) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with K := z.S c, fl := false })) := by
  have hne : rK ≠ rS c := by fin_cases c <;> decide
  have h' := cpy_run (W := W) (toSt z) hr rK (rS c) hne (by show rgv z (rS c) < 2 ^ W; rw [get_S]; exact h)
  refine h'.congr_out (fixR (z' := { z with K := z.S c, fl := false }) rfl rfl ?_ rfl)
  show Function.update (rgv z) rK (rgv z (rS c)) = _
  rw [get_S, set_K]
  rfl

end Regs

/-! ## One signed number, and a run of them -/

/-- The signed numbers of one exact child: its weights, then its target. -/
def zs {A : ℕ} (g : ExactThresholdGate A) : List ℤ := List.ofFn g.weight ++ [g.target]

theorem exactWord_zs {A : ℕ} (g : ExactThresholdGate A) : exactWord g = (zs g).flatMap intWord := by
  simp [exactWord, zs, List.flatMap_append]

theorem zs_length {A : ℕ} (g : ExactThresholdGate A) : (zs g).length = A + 1 := by simp [zs]

theorem intWord_len (w : ℤ) : (intWord w).length = (natWord w.natAbs).length + 1 := by simp [intWord]

theorem natBitLength_le_len (x : ℕ) : natBitLength x ≤ (natWord x).length := by
  rw [ReadNat.natWord_length]; omega

/-- `flag := sign; X := |w|`. -/
def rdInt (c : Fin 4) :=
  Composition.machine (mBit (NR := 24) (NO := 29) (ocm c) (ocs c)) (mReadNat (NR := 24) (NO := 29) (ocs c) (ocm c) rX)

section Int
variable {W : ℕ} (z : TZ) (hr : z.rl = .ruler) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool)
include hr

theorem rdInt_run (q : ℕ) (w : ℤ) (pre post : List Bool) (hpay : pay = pre ++ intWord w ++ post)
    (hq : q = pre.length + 1) (hz : z.cc = strm base c pay q) (hW : pay.length ≤ W) :
    LRuns W (rdInt c) (1 + 1 + (3 * W + 5)) (roles (toSt z))
      (roles (toSt { z with cc := strm base c pay (q + (intWord w).length), X := w.natAbs, fl := decide (w < 0) })) := by
  have hsg : sf pay q = decide (w < 0) := by
    rw [hpay, hq, sf_succ, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
    simp [intWord]
  have e1 := rbit (W := W) z base c pay q hz
  rw [hsg] at e1
  have hpay' : pay = (pre ++ [decide (w < 0)]) ++ natWord w.natAbs ++ post := by
    rw [hpay]; simp [intWord]
  have e2 := rnX (W := W) { z with cc := strm base c pay (q + 1), fl := decide (w < 0) } hr base c pay (q + 1)
    w.natAbs rfl (by
      have h1 := natBitLength_le_len w.natAbs
      have h2 : (natWord w.natAbs).length ≤ pay.length := by rw [hpay']; simp; omega
      omega)
    (hS_of pay (q + 1) w.natAbs (pre ++ [decide (w < 0)]) post hpay' (by simp [hq]))
  have e := e1.seq e2
  rw [show q + 1 + (natWord w.natAbs).length = q + (intWord w).length by rw [intWord_len]; omega] at e
  exact e

end Int

/-- Skip one run of signed numbers (the loop counter `I` counts them). -/
def skipBody (c : Fin 4) :=
  Composition.machine (rdInt c) (Composition.machine (mZero (NO := 29) rX) (mDec (NO := 29) rI))

def skipOne (c : Fin 4) := Loop (mPos (NO := 29) rI) (skipBody c) FL

def skipBodyCost (W : ℕ) : ℕ := (1 + 1 + (3 * W + 5)) + 1 + ((2 * W + 3) + 1 + (2 * W + 3))

/-- The state inside `skipOne`. -/
def skSt (z0 : TZ) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q0 : ℕ) (zl : List ℤ) (i : ℕ) (f : Bool) : TZ :=
  { z0 with cc := strm base c pay (q0 + ((zl.take i).flatMap intWord).length), I := zl.length - i, X := 0, fl := f }

theorem flatMap_take_succ (zl : List ℤ) (i : ℕ) (hi : i < zl.length) :
    ((zl.take (i + 1)).flatMap intWord).length = ((zl.take i).flatMap intWord).length + (intWord zl[i]).length := by
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append, List.length_append]
  simp

theorem flatMap_split (zl : List ℤ) (i : ℕ) (hi : i < zl.length) :
    zl.flatMap intWord = (zl.take i).flatMap intWord ++ intWord zl[i] ++ (zl.drop (i + 1)).flatMap intWord := by
  have h := List.take_append_drop i zl
  rw [List.drop_eq_getElem_cons hi] at h
  conv_lhs => rw [← h]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

section Skip
variable {W : ℕ} (z0 : TZ) (hr : z0.rl = .ruler) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool)
include hr

theorem skipOne_run (zl : List ℤ) (pre0 post0 : List Bool) (hpay : pay = pre0 ++ zl.flatMap intWord ++ post0)
    (hW : pay.length ≤ W) (hIW : zl.length < 2 ^ W) :
    LRuns W (skipOne c) ((zl.length + 1) * ((2 * W + 3) + skipBodyCost W + 2))
      (roles (toSt (skSt z0 base c pay (pre0.length + 1) zl 0 false)))
      (roles (toSt (skSt z0 base c pay (pre0.length + 1) zl zl.length false))) := by
  have hl := Loop.runs (W := W) (mPos (NO := 29) rI) (skipBody c) FL
    (fun i => roles (toSt (skSt z0 base c pay (pre0.length + 1) zl i false)))
    (fun i => roles (toSt (skSt z0 base c pay (pre0.length + 1) zl i (decide (i < zl.length))))) zl.length
    (fun i hi => by
      have h := posI (W := W) (skSt z0 base c pay (pre0.length + 1) zl i false) hr
        (by show zl.length - i < 2 ^ W; omega)
      refine h.congr_out (congrArg (fun f => roles (toSt { skSt z0 base c pay (pre0.length + 1) zl i false with fl := f }))
        ?_)
      show decide (0 < zl.length - i) = decide (i < zl.length)
      apply dec_congr; omega)
    (fun i _ => rfl)
    (fun i hi => by
      have e1 := rdInt_run (W := W) (skSt z0 base c pay (pre0.length + 1) zl i (decide (i < zl.length))) hr base c pay
        (pre0.length + 1 + ((zl.take i).flatMap intWord).length) zl[i]
        (pre0 ++ (zl.take i).flatMap intWord) ((zl.drop (i + 1)).flatMap intWord ++ post0)
        (by rw [hpay, flatMap_split zl i hi]; simp [List.append_assoc]) (by simp; omega) rfl hW
      set st1 : TZ := { skSt z0 base c pay (pre0.length + 1) zl i (decide (i < zl.length)) with
        cc := strm base c pay (pre0.length + 1 + ((zl.take i).flatMap intWord).length + (intWord zl[i]).length),
        X := zl[i].natAbs, fl := decide (zl[i] < 0) } with hst1
      have e2 := zX (W := W) st1 hr
      have e3 := decI (W := W) { st1 with X := 0, fl := false } hr (by show zl.length - i < 2 ^ W; omega)
        (by show 1 ≤ zl.length - i; omega)
      refine (e1.seq (e2.seq e3)).congr_out (congrArg (fun z => roles (toSt z)) ?_)
      simp only [skSt]
      rw [flatMap_take_succ zl i hi, Nat.add_assoc]
      congr 1
      show strm base c pay (pre0.length + 1 + ((zl.take i).flatMap intWord).length + (intWord zl[i]).length) = _
      congr 1
      omega)
  exact hl.congr_out (congrArg (fun f => roles (toSt (skSt z0 base c pay (pre0.length + 1) zl zl.length f)))
    (by simp))

end Skip

/-! ## Skipping whole children -/

def skipAllBody (c : Fin 4) :=
  Composition.machine (mCpy (NO := 29) rI rA) (Composition.machine (mInc (NO := 29) rI)
    (Composition.machine (skipOne c) (mDec (NO := 29) rK)))

def skipAll (c : Fin 4) := Loop (mPos (NO := 29) rK) (skipAllBody c) FL

def skipAllBodyCost (W A : ℕ) : ℕ :=
  (2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((A + 1 + 1) * ((2 * W + 3) + skipBodyCost W + 2) + 1 + (2 * W + 3)))

def skipAllCost (W A s : ℕ) : ℕ := (s + 1) * ((2 * W + 3) + skipAllBodyCost W A + 2)

/-- The state inside `skipAll`: `k` children skipped. -/
def saSt (z0 : TZ) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q0 : ℕ) {A : ℕ}
    (gs : List (ExactThresholdGate A)) (sn k : ℕ) (f : Bool) : TZ :=
  { z0 with cc := strm base c pay (q0 + ((gs.take k).flatMap exactWord).length), K := sn - k, I := 0, X := 0, fl := f }

theorem exact_take_succ {A : ℕ} (gs : List (ExactThresholdGate A)) (k : ℕ) (hk : k < gs.length) :
    ((gs.take (k + 1)).flatMap exactWord).length = ((gs.take k).flatMap exactWord).length +
      ((zs gs[k]).flatMap intWord).length := by
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.length_append]
  simp [List.flatMap_singleton, exactWord_zs]

theorem exact_split {A : ℕ} (gs : List (ExactThresholdGate A)) (k : ℕ) (hk : k < gs.length) :
    gs.flatMap exactWord = (gs.take k).flatMap exactWord ++ (zs gs[k]).flatMap intWord ++
      (gs.drop (k + 1)).flatMap exactWord := by
  have h := List.take_append_drop k gs
  rw [List.drop_eq_getElem_cons hk] at h
  conv_lhs => rw [← h]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc, exactWord_zs]

section SkipAll
variable {W : ℕ} (z0 : TZ) (hr : z0.rl = .ruler) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool)
include hr

theorem skipAll_run {A : ℕ} (gs : List (ExactThresholdGate A)) (sn : ℕ) (hsn : sn ≤ gs.length)
    (pre post : List Bool) (hpay : pay = pre ++ gs.flatMap exactWord ++ post) (hA : z0.A = A)
    (hW : pay.length ≤ W) (hAW : A + 2 < 2 ^ W) (hsW : sn < 2 ^ W) :
    LRuns W (skipAll c) (skipAllCost W A sn)
      (roles (toSt (saSt z0 base c pay (pre.length + 1) gs sn 0 false)))
      (roles (toSt (saSt z0 base c pay (pre.length + 1) gs sn sn false))) := by
  have hl := Loop.runs (W := W) (nb := skipAllBodyCost W A) (mPos (NO := 29) rK) (skipAllBody c) FL
    (fun k => roles (toSt (saSt z0 base c pay (pre.length + 1) gs sn k false)))
    (fun k => roles (toSt (saSt z0 base c pay (pre.length + 1) gs sn k (decide (k < sn))))) sn
    (fun k hk => by
      have h := posK (W := W) (saSt z0 base c pay (pre.length + 1) gs sn k false) hr
        (by show sn - k < 2 ^ W; omega)
      refine h.congr_out (congrArg (fun f => roles (toSt { saSt z0 base c pay (pre.length + 1) gs sn k false with fl := f }))
        ?_)
      show decide (0 < sn - k) = decide (k < sn)
      apply dec_congr; omega)
    (fun k _ => rfl)
    (fun k hk => by
      have hkg : k < gs.length := by omega
      set τk := saSt z0 base c pay (pre.length + 1) gs sn k (decide (k < sn)) with hτk
      have e1 := cpyIA (W := W) τk hr (by show z0.A < 2 ^ W; omega)
      have e2 := incI (W := W) { τk with I := τk.A, fl := false } hr (by show z0.A + 1 < 2 ^ W; omega)
      set pre1 := pre ++ (gs.take k).flatMap exactWord with hpre1
      have hpay1 : pay = pre1 ++ (zs gs[k]).flatMap intWord ++ ((gs.drop (k + 1)).flatMap exactWord ++ post) := by
        rw [hpay, exact_split gs k hkg]; simp [hpre1, List.append_assoc]
      have e3 := skipOne_run (W := W) { { τk with I := τk.A, fl := false } with I := τk.A + 1, fl := false } hr base c pay
        (zs gs[k]) pre1 ((gs.drop (k + 1)).flatMap exactWord ++ post) hpay1 hW
        (by rw [zs_length]; omega)
      have hs0 : skSt { { τk with I := τk.A, fl := false } with I := τk.A + 1, fl := false } base c pay (pre1.length + 1)
          (zs gs[k]) 0 false = { { τk with I := τk.A, fl := false } with I := τk.A + 1, fl := false } := by
        simp only [skSt, List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero, zs_length, Nat.sub_zero, hτk,
          saSt, hpre1, List.length_append, hA]
        congr 1
        · congr 1; omega
      rw [hs0] at e3
      set st3 := skSt { { τk with I := τk.A, fl := false } with I := τk.A + 1, fl := false } base c pay (pre1.length + 1)
        (zs gs[k]) (zs gs[k]).length false with hst3
      have e4 := decK (W := W) st3 hr (by show sn - k < 2 ^ W; omega) (by show 1 ≤ sn - k; omega)
      refine ((e1.seq (e2.seq (e3.seq e4))).congr_out (congrArg (fun z => roles (toSt z)) ?_)).enlarge ?_
      · simp only [hst3, skSt, saSt, hτk, hpre1, List.length_append, Nat.sub_self, List.take_length]
        rw [exact_take_succ gs k hkg]
        congr 1
        · congr 1; omega
      · unfold skipAllBodyCost
        rw [zs_length])
  exact hl.congr_out (congrArg (fun f => roles (toSt (saSt z0 base c pay (pre.length + 1) gs sn sn f)))
    (by simp))

end SkipAll

/-! ## Seek: arity, child count, skip the unselected children -/

def seek (c : Fin 4) :=
  Composition.machine (mReadNat (NR := 24) (NO := 29) (ocs c) (ocm c) rA)
    (Composition.machine (mReadNat (NR := 24) (NO := 29) (ocs c) (ocm c) rX)
      (Composition.machine (mZero (NO := 29) rX) (Composition.machine (mCpy (NO := 29) rK (rS c)) (skipAll c))))

def seekCost (W A s : ℕ) : ℕ :=
  (3 * W + 5) + 1 + ((3 * W + 5) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + skipAllCost W A s)))

section Seek
variable {W : ℕ} (z : TZ) (hr : z.rl = .ruler) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool)
include hr

theorem seek_run {A : ℕ} (gs : List (ExactThresholdGate A)) (hz : z.cc = strm base c pay 1)
    (hpay : pay = natWord A ++ natWord gs.length ++ gs.flatMap exactWord) (hI : z.I = 0)
    (hsel : z.S c ≤ gs.length) (hW : pay.length ≤ W) (hAW : A + 2 < 2 ^ W) (hsW : gs.length < 2 ^ W) :
    LRuns W (seek c) (seekCost W A (z.S c)) (roles (toSt z))
      (roles (toSt (saSt { z with A := A } base c pay ((natWord A ++ natWord gs.length).length + 1) gs (z.S c)
        (z.S c) false))) := by
  have hbl : ∀ x, x < 2 ^ (natWord x).length := fun x =>
    lt_of_lt_of_le (ReadNat.lt_natBitLength x) (Nat.pow_le_pow_right (by norm_num) (natBitLength_le_len x))
  have e1 := rnA (W := W) z hr base c pay 1 A hz
    (by have := natBitLength_le_len A; have : (natWord A).length ≤ pay.length := by rw [hpay]; simp
        omega)
    (hS_of pay 1 A [] (natWord gs.length ++ gs.flatMap exactWord) (by rw [hpay]; simp) rfl)
  have e2 := rnX (W := W) { z with cc := strm base c pay (1 + (natWord A).length), A := A } hr base c pay
    (1 + (natWord A).length) gs.length rfl
    (by have := natBitLength_le_len gs.length
        have : (natWord gs.length).length ≤ pay.length := by rw [hpay]; simp; omega
        omega)
    (hS_of pay _ gs.length (natWord A) (gs.flatMap exactWord) (by rw [hpay]) (by omega))
  have e3 := zX (W := W) { { z with cc := strm base c pay (1 + (natWord A).length), A := A } with
    cc := strm base c pay (1 + (natWord A).length + (natWord gs.length).length), X := gs.length } hr
  have e4 := cpyKS (W := W) { { { z with cc := strm base c pay (1 + (natWord A).length), A := A } with
    cc := strm base c pay (1 + (natWord A).length + (natWord gs.length).length), X := gs.length } with
    X := 0, fl := false } hr c (by show z.S c < 2 ^ W; omega)
  have e5 := skipAll_run (W := W) { z with A := A } hr base c pay gs (z.S c) hsel (natWord A ++ natWord gs.length) []
    (by rw [hpay]; simp) rfl hW hAW (by omega)
  have hs0 : saSt { z with A := A } base c pay ((natWord A ++ natWord gs.length).length + 1) gs (z.S c) 0 false =
      { { { { z with cc := strm base c pay (1 + (natWord A).length), A := A } with
        cc := strm base c pay (1 + (natWord A).length + (natWord gs.length).length), X := gs.length } with
        X := 0, fl := false } with K := z.S c, fl := false } := by
    simp only [saSt, List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero, Nat.sub_zero,
      List.length_append, hI]
    congr 2
    omega
  rw [hs0] at e5
  exact e1.seq (e2.seq (e3.seq (e4.seq e5)))

end Seek

end
end NearCubicWires.PacketsKeys.ThrProg

