import Proof.Packets.PacketsKeysThrSeek

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
open NearCubicWires.RepairRepresentation NearCubicWires.ThresholdAlignedEnvelope
noncomputable section

theorem zs_mag {A : ℕ} (g : ExactThresholdGate A) : ((zs g).map Int.natAbs).sum = childMagnitude g := by
  simp [zs, childMagnitude, List.sum_ofFn]

/-! ## The sum loop -/

def sumBody (c : Fin 4) :=
  Composition.machine (rdInt c) (Composition.machine (mAdd (NO := 29) rB rX)
    (Composition.machine (mZero (NO := 29) rX) (mDec (NO := 29) rI)))

def sumLoop (c : Fin 4) := Loop (mPos (NO := 29) rI) (sumBody c) FL

def sumBodyCost (W : ℕ) : ℕ := (1 + 1 + (3 * W + 5)) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3)))

def suSt (z0 : TZ) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q0 : ℕ) (zl : List ℤ) (i : ℕ) (f : Bool) : TZ :=
  { z0 with cc := strm base c pay (q0 + ((zl.take i).flatMap intWord).length), I := zl.length - i, X := 0, B := z0.B + ((zl.take i).map Int.natAbs).sum, fl := f }

theorem sum_take_succ (zl : List ℤ) (i : ℕ) (hi : i < zl.length) :
    ((zl.take (i + 1)).map Int.natAbs).sum = ((zl.take i).map Int.natAbs).sum + zl[i].natAbs := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  simp

section Sum
variable {W : ℕ} (z0 : TZ) (hr : z0.rl = .ruler) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool)
include hr

theorem sumLoop_run (zl : List ℤ) (pre0 post0 : List Bool) (hpay : pay = pre0 ++ zl.flatMap intWord ++ post0)
    (hW : pay.length ≤ W) (hIW : zl.length < 2 ^ W) (hB : z0.B + (zl.map Int.natAbs).sum < 2 ^ W) :
    LRuns W (sumLoop c) ((zl.length + 1) * ((2 * W + 3) + sumBodyCost W + 2))
      (roles (toSt (suSt z0 base c pay (pre0.length + 1) zl 0 false)))
      (roles (toSt (suSt z0 base c pay (pre0.length + 1) zl zl.length false))) := by
  have hmono : ∀ i, i ≤ zl.length → ((zl.take i).map Int.natAbs).sum ≤ (zl.map Int.natAbs).sum := by
    intro i _
    exact List.Sublist.sum_le_sum ((List.take_sublist i zl).map _) (fun _ _ => Nat.zero_le _)
  have hl := Loop.runs (W := W) (mPos (NO := 29) rI) (sumBody c) FL
    (fun i => roles (toSt (suSt z0 base c pay (pre0.length + 1) zl i false)))
    (fun i => roles (toSt (suSt z0 base c pay (pre0.length + 1) zl i (decide (i < zl.length))))) zl.length
    (fun i hi => by
      have h := posI (W := W) (suSt z0 base c pay (pre0.length + 1) zl i false) hr
        (by show zl.length - i < 2 ^ W; omega)
      refine h.congr_out (congrArg (fun f => roles (toSt { suSt z0 base c pay (pre0.length + 1) zl i false with fl := f }))
        ?_)
      show decide (0 < zl.length - i) = decide (i < zl.length)
      apply dec_congr; omega)
    (fun i _ => rfl)
    (fun i hi => by
      have hs := hmono (i + 1) hi
      rw [sum_take_succ zl i hi] at hs
      have e1 := rdInt_run (W := W) (suSt z0 base c pay (pre0.length + 1) zl i (decide (i < zl.length))) hr base c pay
        (pre0.length + 1 + ((zl.take i).flatMap intWord).length) zl[i]
        (pre0 ++ (zl.take i).flatMap intWord) ((zl.drop (i + 1)).flatMap intWord ++ post0)
        (by rw [hpay, flatMap_split zl i hi]; simp [List.append_assoc]) (by simp; omega) rfl hW
      set st1 : TZ := { suSt z0 base c pay (pre0.length + 1) zl i (decide (i < zl.length)) with
        cc := strm base c pay (pre0.length + 1 + ((zl.take i).flatMap intWord).length + (intWord zl[i]).length),
        X := zl[i].natAbs, fl := decide (zl[i] < 0) } with hst1
      have e2 := (add_run (W := W) (toSt st1) hr rB rX (by decide) (by show z0.B + _ < 2 ^ W; omega)
        (by show zl[i].natAbs < 2 ^ W; omega) (by show z0.B + _ + zl[i].natAbs < 2 ^ W; omega)).congr_out
        (fixR (z' := { st1 with B := st1.B + st1.X, fl := false }) rfl rfl (set_B st1 _) rfl)
      have e3 := zX (W := W) { st1 with B := st1.B + st1.X, fl := false } hr
      have e4 := decI (W := W) { { st1 with B := st1.B + st1.X, fl := false } with X := 0, fl := false } hr
        (by show zl.length - i < 2 ^ W; omega) (by show 1 ≤ zl.length - i; omega)
      refine (e1.seq (e2.seq (e3.seq e4))).congr_out (congrArg (fun z => roles (toSt z)) ?_)
      simp only [suSt, hst1]
      rw [flatMap_take_succ zl i hi, sum_take_succ zl i hi, Nat.add_assoc]
      congr 1
      · show strm base c pay (pre0.length + 1 + ((zl.take i).flatMap intWord).length + (intWord zl[i]).length) = _
        congr 1
        omega
      all_goals omega)
  exact hl.congr_out (congrArg (fun f => roles (toSt (suSt z0 base c pay (pre0.length + 1) zl zl.length f)))
    (by simp))

end Sum

/-! ## Top-stream and circuit-tape steps -/

section Tape
variable {W : ℕ} (z : TZ)

theorem peekT (f : ℕ → Bool) (sp : ℕ) (hts : z.ts = .cells f sp) :
    LRuns W (mPeek (NR := 24) (NO := 29) oTS) 1 (roles (toSt z)) (roles (toSt { z with fl := f sp })) :=
  (peek_run (W := W) (toSt z) oTS f sp hts).congr_out (fixR (z' := { z with fl := f sp }) rfl rfl rfl rfl)

theorem unfC (c : Fin 4) (tw pay : List Bool) (sp : ℕ)
    (hX : ∀ i, i < (RepairOrdinary.frame pay).length → sf tw (sp + i) = (RepairOrdinary.frame pay).getD i false)
    (hts : z.ts = .cells (sf tw) sp) (hcs : z.cc (cs c) = .cells blank 0) (hcm : z.cc (cm c) = .cells blank 0) :
    LRuns W (mUnf (NR := 24) (NO := 29) oTS (ocs c) (ocm c)) (5 * pay.length + 10) (roles (toSt z))
      (roles (toSt { z with ts := .cells (sf tw) (sp + (RepairOrdinary.frame pay).length), cc := strm z.cc c pay 1 })) := by
  have h := unf_run (W := W) (toSt z) oTS (ocs c) (ocm c) (by simp [ocs]; omega) (by simp [ocm]; omega) (ocs_ocm c) sp pay (sf tw) hX
    hts (by show otv z (ocs c) = _; rw [get_cs, hcs]) (by show otv z (ocm c) = _; rw [get_cm, hcm])
  refine h.congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (Function.update (otv z) oTS _) (ocs c) _) (ocm c) _ = _
  rw [oset_ts, oset2]
  rfl

theorem rewC (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : q ≤ pay.length + 1) (hz : z.cc = strm base c pay q) :
    LRuns W (mRew (NR := 24) (NO := 29) (ocm c) (ocs c)) (q + 4) (roles (toSt z))
      (roles (toSt { z with cc := strm base c pay 1 })) := by
  have h := rew_run (W := W) (toSt z) (ocm c) (ocs c) (Ne.symm (ocs_ocm c)) pay.length q (sf pay) hq1 hq
    (by show otv z (ocm c) = _; rw [get_cm, hz, strm_cm]; rfl) (by show otv z (ocs c) = _; rw [get_cs, hz, strm_cs])
  refine h.congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (otv z) (ocm c) _) (ocs c) _ = _
  rw [oset2', hz]
  exact congrArg (fun t => otv { z with cc := t }) (strm_sm base c pay q 1)

end Tape

/-! ## Pass-1 block -/

def p1Tail (c : Fin 4) :=
  Composition.machine (mCpy (NO := 29) rI rA) (Composition.machine (mInc (NO := 29) rI)
    (Composition.machine (sumLoop c) (Composition.machine (mRew (NR := 24) (NO := 29) (ocm c) (ocs c))
      (mZero (NO := 29) rA))))

def p1Body (c : Fin 4) :=
  Composition.machine (mUnf (NR := 24) (NO := 29) oTS (ocs c) (ocm c)) (Composition.machine (seek c) (p1Tail c))

def p1Block (c : Fin 4) := Ite (mPeek (NR := 24) (NO := 29) oTS) (p1Body c) (nop (4 + 24 + 29)) FL

def p1BodyCost (W A s n : ℕ) : ℕ :=
  (5 * n + 10) + 1 + (seekCost W A s + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 +
    ((A + 1 + 1) * ((2 * W + 3) + sumBodyCost W + 2) + 1 + ((n + 1 + 4) + 1 + (2 * W + 3))))))

/-- The pass-1 block's states: the fields it changes, over a base state. -/
def p1S (z : TZ) (ts : TS) (cc : Fin 8 → TS) (A K I X B : ℕ) (f : Bool) : TZ :=
  { z with ts := ts, cc := cc, A := A, K := K, I := I, X := X, B := B, fl := f }

section Block
variable {W : ℕ} (z : TZ) (hr : z.rl = .ruler) (c : Fin 4)
include hr

theorem p1Body_run (tw pre post pay : List Bool) {A : ℕ} (gs : List (ExactThresholdGate A))
    (htw : tw = pre ++ RepairOrdinary.frame pay ++ post) (hts : z.ts = .cells (sf tw) (pre.length + 1))
    (hpay : pay = natWord A ++ natWord gs.length ++ gs.flatMap exactWord)
    (hcs : z.cc (cs c) = .cells blank 0) (hcm : z.cc (cm c) = .cells blank 0) (hI : z.I = 0)
    (hsel : z.S c < gs.length) (hW : pay.length ≤ W) (hAW : A + 2 < 2 ^ W) (hgW : gs.length < 2 ^ W)
    (hB : z.B + childMagnitude gs[z.S c] < 2 ^ W) :
    LRuns W (p1Body c) (p1BodyCost W A (z.S c) pay.length)
      (roles (toSt (p1S z z.ts z.cc z.A z.K z.I z.X z.B true)))
      (roles (toSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length)) (strm z.cc c pay 1)
        0 0 0 0 (z.B + childMagnitude gs[z.S c]) false))) := by
  have hsn : z.S c < gs.length := hsel
  have e1 : LRuns W (mUnf (NR := 24) (NO := 29) oTS (ocs c) (ocm c)) (5 * pay.length + 10)
      (roles (toSt (p1S z z.ts z.cc z.A z.K z.I z.X z.B true)))
      (roles (toSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length)) (strm z.cc c pay 1)
        z.A z.K z.I z.X z.B true))) :=
    unfC (W := W) (p1S z z.ts z.cc z.A z.K z.I z.X z.B true) c tw pay (pre.length + 1)
      (by intro i hi; rw [htw, show pre.length + 1 + i = pre.length + i + 1 by omega, sf_succ, List.append_assoc,
        List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, List.getD_append _ _ _ _ hi]) hts hcs hcm
  have e2 : LRuns W (seek c) (seekCost W A (z.S c))
      (roles (toSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length)) (strm z.cc c pay 1)
        z.A z.K z.I z.X z.B true)))
      (roles (toSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
        (strm z.cc c pay ((natWord A ++ natWord gs.length).length + 1 + ((gs.take (z.S c)).flatMap exactWord).length))
        A (z.S c - z.S c) 0 0 z.B false))) :=
    seek_run (W := W) (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length)) (strm z.cc c pay 1)
      z.A z.K z.I z.X z.B true) hr z.cc c pay gs rfl hpay hI hsel.le hW hAW hgW
  have e3 := cpyIA (W := W) (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
    (strm z.cc c pay ((natWord A ++ natWord gs.length).length + 1 + ((gs.take (z.S c)).flatMap exactWord).length))
    A (z.S c - z.S c) 0 0 z.B false) hr (by show A < 2 ^ W; omega)
  have e4 := incI (W := W) (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
    (strm z.cc c pay ((natWord A ++ natWord gs.length).length + 1 + ((gs.take (z.S c)).flatMap exactWord).length))
    A (z.S c - z.S c) A 0 z.B false) hr (by show A + 1 < 2 ^ W; omega)
  have hpay1 : pay = (natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord) ++
      (zs gs[z.S c]).flatMap intWord ++ ((gs.drop (z.S c + 1)).flatMap exactWord) := by
    rw [hpay, exact_split gs (z.S c) hsel]; simp [List.append_assoc]
  have hmag := zs_mag gs[z.S c]
  have e5 := sumLoop_run (W := W) (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
    (strm z.cc c pay 1) A (z.S c - z.S c) (A + 1) 0 z.B false) hr z.cc c pay
    (zs gs[z.S c]) (natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord)
    ((gs.drop (z.S c + 1)).flatMap exactWord) hpay1 hW (by rw [zs_length]; omega)
    (by show z.B + _ < 2 ^ W; rw [hmag]; exact hB)
  have hC : strm z.cc c pay ((natWord A ++ natWord gs.length).length + 1 + ((gs.take (z.S c)).flatMap exactWord).length) =
      strm z.cc c pay ((natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1) := by
    congr 1; simp; omega
  have hA1 : A + 1 = (zs gs[z.S c]).length := (zs_length _).symm
  have b45 : roles (toSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
      (strm z.cc c pay ((natWord A ++ natWord gs.length).length + 1 + ((gs.take (z.S c)).flatMap exactWord).length))
      A (z.S c - z.S c) (A + 1) 0 z.B false)) =
      roles (toSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
      (strm z.cc c pay ((natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1))
      A (z.S c - z.S c) (zs gs[z.S c]).length 0 z.B false)) := by
    rw [hC, hA1]
  have e4' := e4.congr_out b45
  have hq5 : (natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1 +
      (((zs gs[z.S c]).take (zs gs[z.S c]).length).flatMap intWord).length ≤ pay.length + 1 := by
    rw [List.take_length]; conv_rhs => rw [hpay1]
    simp; omega
  have e6 := rewC (W := W) (suSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
    (strm z.cc c pay 1) A (z.S c - z.S c) (A + 1) 0 z.B false) z.cc c pay
    ((natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1)
    (zs gs[z.S c]) (zs gs[z.S c]).length false) z.cc c pay
    ((natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1 +
      (((zs gs[z.S c]).take (zs gs[z.S c]).length).flatMap intWord).length) (by omega) hq5 rfl
  have e7 := zA (W := W) { suSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
    (strm z.cc c pay 1) A (z.S c - z.S c) (A + 1) 0 z.B false) z.cc c pay
    ((natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1)
    (zs gs[z.S c]) (zs gs[z.S c]).length false with cc := strm z.cc c pay 1 } hr
  have hall := e1.seq (e2.seq (e3.seq (e4'.seq (e5.seq (e6.seq e7)))))
  have hK : z.S c - z.S c = 0 := Nat.sub_self _
  have hI0 : (zs gs[z.S c]).length - (zs gs[z.S c]).length = 0 := Nat.sub_self _
  have hBf : z.B + (((zs gs[z.S c]).take (zs gs[z.S c]).length).map Int.natAbs).sum = z.B + childMagnitude gs[z.S c] := by
    rw [List.take_length, hmag]
  have bf : roles (toSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length))
      (strm z.cc c pay 1) 0 (z.S c - z.S c) ((zs gs[z.S c]).length - (zs gs[z.S c]).length) 0
      (z.B + (((zs gs[z.S c]).take (zs gs[z.S c]).length).map Int.natAbs).sum) false)) =
      roles (toSt (p1S z (.cells (sf tw) (pre.length + 1 + (RepairOrdinary.frame pay).length)) (strm z.cc c pay 1)
        0 0 0 0 (z.B + childMagnitude gs[z.S c]) false)) := by
    rw [hK, hI0, hBf]
  refine (hall.congr_out bf).enlarge ?_
  unfold p1BodyCost
  rw [List.take_length] at hq5
  rw [List.take_length, zs_length]
  omega

end Block

/-! ## The pass-1 chain -/

def p1BlockCost (W : ℕ) : ℕ := 1 + p1BodyCost W W W W + 0 + 2

theorem p1BodyCost_mono (W A s n : ℕ) (hA : A ≤ W) (hs : s ≤ W) (hn : n ≤ W) :
    p1BodyCost W A s n ≤ p1BodyCost W W W W := by
  unfold p1BodyCost seekCost skipAllCost skipAllBodyCost
  have h1 : (s + 1) * (2 * W + 3 + (2 * W + 3 + 1 + (2 * W + 3 + 1 + ((A + 1 + 1) * (2 * W + 3 + skipBodyCost W + 2) + 1
      + (2 * W + 3)))) + 2) ≤ (W + 1) * (2 * W + 3 + (2 * W + 3 + 1 + (2 * W + 3 + 1 + ((W + 1 + 1) *
      (2 * W + 3 + skipBodyCost W + 2) + 1 + (2 * W + 3)))) + 2) := by gcongr
  have h2 : (A + 1 + 1) * (2 * W + 3 + sumBodyCost W + 2) ≤ (W + 1 + 1) * (2 * W + 3 + sumBodyCost W + 2) := by gcongr
  omega

section Chain1
variable {α : Type} (ar : α → ℕ) (ch : (x : α) → List (ExactThresholdGate (ar x)))

/-- One circuit's top payload. -/
def payOf (x : α) : List Bool := natWord (ar x) ++ natWord (ch x).length ++ (ch x).flatMap exactWord

/-- The circuit tapes after pass-1 blocks: payloads rewound to cursor 1. -/
def ccP (pays : List (List Bool)) (base : Fin 8 → TS) : Fin 8 → TS := fun k =>
  if h : k.val / 2 < pays.length then
    (if k.val % 2 = 0 then .cells (sf pays[k.val / 2]) 1 else .cells (mks pays[k.val / 2]) 1)
  else base k

theorem ccP_snoc (pays : List (List Bool)) (base : Fin 8 → TS) (c : Fin 4) (hc : c.val = pays.length)
    (pay : List Bool) : strm (ccP pays base) c pay 1 = ccP (pays ++ [pay]) base := by
  funext k
  unfold strm
  by_cases hk1 : k = cm c
  · subst hk1
    rw [Function.update_self]
    unfold ccP
    have h2 : (cm c).val / 2 = pays.length := by simp [cm]; omega
    have h3 : (cm c).val % 2 = 1 := by simp [cm]
    rw [dif_pos (by simp; omega), if_neg (by omega)]
    congr 2
    simp only [h2, List.getElem_append_right (le_refl _), Nat.sub_self]
    rfl
  · rw [Function.update_of_ne hk1]
    by_cases hk2 : k = cs c
    · subst hk2
      rw [Function.update_self]
      unfold ccP
      have h2 : (cs c).val / 2 = pays.length := by simp [cs]; omega
      have h3 : (cs c).val % 2 = 0 := by simp [cs]
      rw [dif_pos (by simp; omega), if_pos h3]
      congr 2
      simp only [h2, List.getElem_append_right (le_refl _), Nat.sub_self]
      rfl
    · rw [Function.update_of_ne hk2]
      have hne : k.val / 2 ≠ pays.length := by
        intro e
        rcases Nat.even_or_odd k.val with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact hk2 (Fin.ext (by simp [cs]; omega))
        · exact hk1 (Fin.ext (by simp [cm]; omega))
      unfold ccP
      by_cases hlt : k.val / 2 < pays.length
      · rw [dif_pos hlt, dif_pos (by simp; omega)]
        split_ifs <;> simp [List.getElem_append_left hlt]
      · rw [dif_neg hlt, dif_neg (by simp; omega)]

theorem ccP_cs (pays : List (List Bool)) (base : Fin 8 → TS) (c : Fin 4) (hc : pays.length ≤ c.val) :
    ccP pays base (cs c) = base (cs c) := by
  unfold ccP; rw [dif_neg (by simp [cs]; omega)]

theorem ccP_cm (pays : List (List Bool)) (base : Fin 8 → TS) (c : Fin 4) (hc : pays.length ≤ c.val) :
    ccP pays base (cm c) = base (cm c) := by
  unfold ccP; rw [dif_neg (by simp [cm]; omega)]

end Chain1

/-! ## Pass-1 block runs -/

theorem sf_frame_head (pre pay post : List Bool) (hpay : pay ≠ []) :
    sf (pre ++ RepairOrdinary.frame pay ++ post) (pre.length + 1) = true := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hpay
  rw [sf_succ, List.append_assoc, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem sf_end (w : List Bool) : sf w (w.length + 1) = false := by
  rw [sf_succ, List.getD_eq_default _ _ (le_refl _)]

theorem flatMap_split' {β : Type} (L : List β) (F : β → List Bool) (c : ℕ) (hc : c < L.length) :
    L.flatMap F = (L.take c).flatMap F ++ F L[c] ++ (L.drop (c + 1)).flatMap F := by
  have h := List.take_append_drop c L
  rw [List.drop_eq_getElem_cons hc] at h
  conv_lhs => rw [← h]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

section Chain1b
variable {α : Type} (ar : α → ℕ) (ch : (x : α) → List (ExactThresholdGate (ar x)))

/-- The framed payloads of a circuit list (input part 5 of a THR request). -/
def twOf (L : List α) : List Bool := L.flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))

/-- The state between pass-1 blocks. -/
def st1 (z0 : TZ) (L : List α) (ms : List ℕ) (k : ℕ) : TZ :=
  p1S z0 (.cells (sf (twOf ar ch L)) (((L.take k).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))).length + 1))
    (ccP ((L.take k).map (payOf ar ch)) z0.cc) 0 0 0 0 (z0.B + (ms.take k).sum) false

theorem payOf_ne (x : α) : payOf ar ch x ≠ [] := by
  unfold payOf; simp [natWord, NearCubicWires.WilliamsPublishedForm.framedNatBits]

theorem ar_le_pay (x : α) (hx : ch x ≠ []) : ar x ≤ (payOf ar ch x).length := by
  obtain ⟨g, gs, h⟩ := List.exists_cons_of_ne_nil hx
  have h1 : (exactWord g).length ≤ ((ch x).flatMap exactWord).length := by
    rw [h, List.flatMap_cons, List.length_append]; omega
  have h2 : ar x ≤ (exactWord g).length := by
    rw [exactWord_zs]
    have := zs_length g
    have h3 : (zs g).length ≤ ((zs g).flatMap intWord).length := by
      rw [List.length_flatMap]
      calc (zs g).length = ((zs g).map (fun _ => 1)).sum := by simp
        _ ≤ ((zs g).map (fun w => (intWord w).length)).sum := by
          apply List.sum_le_sum; intro w _; simp [intWord]
    omega
  unfold payOf; simp only [List.length_append]; omega

theorem ch_le_pay (x : α) : (ch x).length ≤ (payOf ar ch x).length := by
  have h : (ch x).length ≤ ((ch x).flatMap exactWord).length := by
    rw [List.length_flatMap]
    calc (ch x).length = ((ch x).map (fun _ => 1)).sum := by simp
      _ ≤ ((ch x).map (fun g => (exactWord g).length)).sum := by
        apply List.sum_le_sum; intro g _
        rw [exactWord_zs]; simp [zs, intWord, List.flatMap_append]; omega
  unfold payOf; simp only [List.length_append]; omega

section Block1
variable {W : ℕ} (z0 : TZ) (hr : z0.rl = .ruler) (L : List α) (ms : List ℕ) (hms : ms.length = L.length)
  (hbase : ∀ k, z0.cc k = .cells blank 0)
  (hsel : ∀ (i : Fin 4) (hi : i.val < L.length), z0.S i < (ch L[i.val]).length)
  (hmag : ∀ (i : Fin 4) (hi : i.val < L.length),
    ms[i.val]'(by omega) = childMagnitude ((ch L[i.val])[z0.S i]'(hsel i hi)))
  (hW : ∀ x ∈ L, (payOf ar ch x).length ≤ W) (hAW : ∀ x ∈ L, ar x + 2 < 2 ^ W)
  (hgW : ∀ x ∈ L, (ch x).length < 2 ^ W) (hBW : z0.B + ms.sum < 2 ^ W)
include hr hms hbase hsel hmag hW hAW hgW hBW

theorem p1Block_run (c : Fin 4) :
    LRuns W (p1Block c) (p1BlockCost W) (roles (toSt (st1 ar ch z0 L ms c.val)))
      (roles (toSt (st1 ar ch z0 L ms (c.val + 1)))) := by
  have hpeek := peekT (W := W) (st1 ar ch z0 L ms c.val) (sf (twOf ar ch L))
    (((L.take c.val).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))).length + 1) rfl
  by_cases hc : c.val < L.length
  · have htw : twOf ar ch L = (L.take c.val).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x)) ++
        RepairOrdinary.frame (payOf ar ch L[c.val]) ++
        (L.drop (c.val + 1)).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x)) :=
      flatMap_split' L _ c.val hc
    have hpk : sf (twOf ar ch L) (((L.take c.val).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))).length + 1) =
        true := by rw [htw]; exact sf_frame_head _ _ _ (payOf_ne ar ch _)
    rw [hpk] at hpeek
    have hmem : L[c.val] ∈ L := List.getElem_mem hc
    have hmsl : (ms.take (c.val + 1)).sum = (ms.take c.val).sum + ms[c.val]'(by omega) := by
      rw [List.take_succ_eq_append_getElem (by omega), List.sum_append]; simp
    have hsum : (ms.take (c.val + 1)).sum ≤ ms.sum :=
      List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ => Nat.zero_le _)
    have hbody := p1Body_run (W := W) (st1 ar ch z0 L ms c.val) hr c (twOf ar ch L)
      ((L.take c.val).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x)))
      ((L.drop (c.val + 1)).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))) (payOf ar ch L[c.val])
      (ch L[c.val]) htw rfl rfl
      (by show ccP _ z0.cc (cs c) = _; rw [ccP_cs _ _ c (by simp only [List.length_map, List.length_take]; omega), hbase])
      (by show ccP _ z0.cc (cm c) = _; rw [ccP_cm _ _ c (by simp only [List.length_map, List.length_take]; omega), hbase])
      rfl (hsel c hc)
      (hW _ hmem) (hAW _ hmem) (hgW _ hmem)
      (by
        have h1 := hmag c hc
        show z0.B + (ms.take c.val).sum + childMagnitude ((ch L[c.val])[z0.S c]'(hsel c hc)) < 2 ^ W
        rw [← h1]; omega)
    have hA : ar L[c.val] ≤ W := le_trans (ar_le_pay ar ch _ (List.ne_nil_of_length_pos (by
      have := hsel c hc; omega))) (hW _ hmem)
    have hS : z0.S c ≤ W := le_trans (le_trans (hsel c hc).le (ch_le_pay ar ch _)) (hW _ hmem)
    have hcost := p1BodyCost_mono W (ar L[c.val]) ((st1 ar ch z0 L ms c.val).S c) (payOf ar ch L[c.val]).length hA hS
      (hW _ hmem)
    have hfin : roles (toSt (p1S (st1 ar ch z0 L ms c.val)
        (.cells (sf (twOf ar ch L)) (((L.take c.val).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))).length +
          1 + (RepairOrdinary.frame (payOf ar ch L[c.val])).length))
        (strm (st1 ar ch z0 L ms c.val).cc c (payOf ar ch L[c.val]) 1) 0 0 0 0
        ((st1 ar ch z0 L ms c.val).B + childMagnitude ((ch L[c.val])[z0.S c]'(hsel c hc))) false)) =
        roles (toSt (st1 ar ch z0 L ms (c.val + 1))) := by
      show roles (toSt (p1S z0 (.cells (sf (twOf ar ch L))
        (((L.take c.val).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))).length +
          1 + (RepairOrdinary.frame (payOf ar ch L[c.val])).length))
        (strm (ccP ((L.take c.val).map (payOf ar ch)) z0.cc) c (payOf ar ch L[c.val]) 1) 0 0 0 0
        (z0.B + (ms.take c.val).sum + childMagnitude ((ch L[c.val])[z0.S c]'(hsel c hc))) false)) =
        roles (toSt (p1S z0 (.cells (sf (twOf ar ch L))
        (((L.take (c.val + 1)).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))).length + 1))
        (ccP ((L.take (c.val + 1)).map (payOf ar ch)) z0.cc) 0 0 0 0 (z0.B + (ms.take (c.val + 1)).sum) false))
      rw [ccP_snoc _ _ c (by simp; omega), hmsl, hmag c hc, List.take_succ_eq_append_getElem hc]
      simp only [List.map_append, List.map_singleton, List.flatMap_append, List.flatMap_singleton, List.length_append,
        Nat.add_assoc]
      congr 4
      omega
    refine (Ite.runs (W := W) (nq := 0) (mPeek (NR := 24) (NO := 29) oTS) (p1Body c) (nop (4 + 24 + 29)) FL true hpeek rfl
      (fun _ => hbody.congr_out hfin) (fun h => absurd h (by simp))).enlarge ?_
    unfold p1BlockCost
    omega
  · have hc' : L.length ≤ c.val := by omega
    have hpk : sf (twOf ar ch L) (((L.take c.val).flatMap (fun x => RepairOrdinary.frame (payOf ar ch x))).length + 1) =
        false := by rw [List.take_of_length_le hc']; exact sf_end _
    rw [hpk] at hpeek
    have hsame : st1 ar ch z0 L ms (c.val + 1) = st1 ar ch z0 L ms c.val := by
      unfold st1
      rw [List.take_of_length_le (by omega), List.take_of_length_le hc', List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)]
    have hn : LRuns W (nop (4 + 24 + 29)) 0 (roles (toSt { st1 ar ch z0 L ms c.val with fl := false }))
        (roles (toSt (st1 ar ch z0 L ms (c.val + 1)))) := by
      rw [hsame]; exact nop_lruns _
    exact Ite.runs (W := W) (np := p1BodyCost W W W W) (nq := 0) (mPeek (NR := 24) (NO := 29) oTS) (p1Body c)
      (nop (4 + 24 + 29)) FL false hpeek rfl (fun h => absurd h (by simp)) (fun _ => hn)

end Block1

/-- **Pass 1**: the four blocks. -/
def p1Pass := Composition.machine (p1Block 0) (Composition.machine (p1Block 1) (Composition.machine (p1Block 2) (p1Block 3)))

def p1PassCost (W : ℕ) : ℕ := p1BlockCost W + 1 + (p1BlockCost W + 1 + (p1BlockCost W + 1 + p1BlockCost W))

theorem p1Pass_run {W : ℕ} (z0 : TZ) (hr : z0.rl = .ruler) (L : List α) (hL : L.length ≤ 4) (ms : List ℕ)
    (hms : ms.length = L.length) (hbase : ∀ k, z0.cc k = .cells blank 0)
    (hsel : ∀ (i : Fin 4) (hi : i.val < L.length), z0.S i < (ch L[i.val]).length)
    (hmag : ∀ (i : Fin 4) (hi : i.val < L.length),
      ms[i.val]'(by omega) = childMagnitude ((ch L[i.val])[z0.S i]'(hsel i hi)))
    (hW : ∀ x ∈ L, (payOf ar ch x).length ≤ W) (hAW : ∀ x ∈ L, ar x + 2 < 2 ^ W)
    (hgW : ∀ x ∈ L, (ch x).length < 2 ^ W) (hBW : z0.B + ms.sum < 2 ^ W) :
    LRuns W p1Pass (p1PassCost W) (roles (toSt (st1 ar ch z0 L ms 0)))
      (roles (toSt (p1S z0 (.cells (sf (twOf ar ch L)) ((twOf ar ch L).length + 1)) (ccP (L.map (payOf ar ch)) z0.cc)
        0 0 0 0 (z0.B + ms.sum) false))) := by
  have b0 := p1Block_run ar ch z0 hr L ms hms hbase hsel hmag hW hAW hgW hBW 0
  have b1 := p1Block_run ar ch z0 hr L ms hms hbase hsel hmag hW hAW hgW hBW 1
  have b2 := p1Block_run ar ch z0 hr L ms hms hbase hsel hmag hW hAW hgW hBW 2
  have b3 := p1Block_run ar ch z0 hr L ms hms hbase hsel hmag hW hAW hgW hBW 3
  have hall := b0.seq (b1.seq (b2.seq b3))
  refine hall.congr_out ?_
  show roles (toSt (st1 ar ch z0 L ms 4)) = _
  unfold st1 twOf
  rw [List.take_of_length_le hL, List.take_of_length_le (by omega)]

end Chain1b

end
end NearCubicWires.PacketsKeys.ThrProg

