import Proof.Packets.PacketsKeysThrChain2

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
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsSymBits
noncomputable section

/-! ## A register loaded from a unary stream at any cursor -/

section LoadG
variable {NR NO : ℕ}

def ldG (s : St NR NO) (x : Fin NR) (d u : Fin NO) (f : ℕ → Bool) (c h : ℕ) (fl : Bool) : St NR NO :=
  { s with rg := Function.update s.rg x c, ot := Function.update (Function.update s.ot d (.cells blank h)) u (.cells f h), fl := fl }

variable {W : ℕ} (s : St NR NO)

theorem loadG_run (hr : s.rl = .ruler) (x : Fin NR) (d u : Fin NO) (hdu : d.val ≠ u.val) (f : ℕ → Bool) (h0 v : ℕ)
    (hf : ∀ i, f (h0 + i) = decide (i < v)) (hv : v < 2 ^ W) (hd : s.ot d = .cells blank h0)
    (hu : s.ot u = .cells f h0) :
    LRuns W (loadU x d u) (loadCost W v) (roles s) (roles (ldG s x d u f v (h0 + v + 1) false)) := by
  have hne : d ≠ u := fun e => hdu (congrArg Fin.val e)
  have h0r := zero_run (W := W) s hr x
  have e0 : ({ s with rg := Function.update s.rg x 0, fl := false } : St NR NO) = ldG s x d u f 0 (h0 + 0) false := by
    refine st_eq rfl rfl rfl ?_
    show s.ot = Function.update (Function.update s.ot d (.cells blank (h0 + 0))) u (.cells f (h0 + 0))
    rw [Nat.add_zero, ← hd, ← hu, Function.update_eq_self, Function.update_eq_self]
  rw [e0] at h0r
  have hl := Loop.runs (W := W) (mBit (NR := NR) d u) (mInc (NO := NO) x) FL
    (fun i => roles (ldG s x d u f i (h0 + i) false)) (fun i => roles (ldG s x d u f i (h0 + i + 1) (decide (i < v)))) v
    (fun i _ => by
      have hb := bit_run (W := W) (ldG s x d u f i (h0 + i) false) d u hdu f blank (h0 + i)
        (by simp [ldG]) (by simp [ldG, Function.update_of_ne hne])
      refine hb.congr_out (congrArg roles (st_eq rfl ?_ rfl ?_))
      · show f (h0 + i) = decide (i < v)
        exact hf i
      · funext k
        simp only [ldG, Function.update_apply]
        split_ifs <;> simp_all)
    (fun i _ => rfl)
    (fun i hi => by
      have hb := inc_run (W := W) (ldG s x d u f i (h0 + i + 1) (decide (i < v))) hr x
        (by simp [ldG]; omega)
      refine hb.congr_out (congrArg roles (st_eq rfl rfl ?_ ?_))
      · simp [ldG]
      · simp only [ldG]; rw [Nat.add_assoc])
  have hall := h0r.seq hl
  refine hall.congr_out (congrArg roles (st_eq rfl ?_ rfl rfl))
  simp [ldG]

end LoadG

/-! ## The prologue's steps on `TZ` -/

section ProSteps
variable {W : ℕ} (z : TZ)

theorem initOutT (ho : z.os = .cells blank 0) (hm : z.om = .cells blank 0) :
    LRuns W (mInitOut (NR := 24) (NO := 29) oOS oOM) 1 (roles (toSt z))
      (roles (toSt { z with os := sS [], om := sM [] })) := by
  refine (initOut_run (W := W) (toSt z) oOS oOM (by decide) ho hm).congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (otv z) oOS _) oOM _ = _
  rw [oset_os, oset_om]

theorem unfT (w : List Bool) (htf : z.tf = .cells (PacketsKeys.Setup.ff w) 0) (hts : z.ts = .cells blank 0)
    (htm : z.tm = .cells blank 0) :
    LRuns W (mUnf (NR := 24) (NO := 29) oTF oTS oTM) (5 * w.length + 10) (roles (toSt z))
      (roles (toSt { z with tf := .cells (PacketsKeys.Setup.ff w) (0 + (RepairOrdinary.frame w).length), ts := .cells (sf w) 1, tm := .cells (sf (List.replicate w.length true)) 1 })) := by
  refine (unf_run (W := W) (toSt z) oTF oTS oTM (by decide) (by decide) (by decide) 0 w (PacketsKeys.Setup.ff w)
    (fun i _ => by simp [PacketsKeys.Setup.ff, readTapeBit]) htf hts htm).congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (Function.update (otv z) oTF _) oTS _) oTM _ = _
  rw [oset_tf, oset_ts, oset_tm]

theorem ruleRT (hr : z.rl = .cells blank 0) :
    LRuns W (mRuleR (NR := 24) (NO := 29)) 1 (roles (toSt z)) (roles (toSt { z with rl := .cells (Ruler.rb 1) 1 })) :=
  (ruleR_run (W := W) (toSt z) hr).congr_out (fixR rfl rfl rfl rfl)

theorem appendRT (w : List Bool) (P : ℕ) (hP : 1 ≤ P) (hr : z.rl = .cells (Ruler.rb P) P)
    (hts : z.ts = .cells (sf w) 1) (htm : z.tm = .cells (sf (List.replicate w.length true)) 1) :
    LRuns W (mAppendR (NR := 24) (NO := 29) 8 oTM oTS) ((8 + 1) * w.length + w.length + 7) (roles (toSt z))
      (roles (toSt { z with rl := .cells (Ruler.rb (P + 8 * w.length)) (P + 8 * w.length) })) :=
  (appendR_run (W := W) (toSt z) 8 (by norm_num) oTM oTS (by decide) w.length P hP (sf w) htm hts hr).congr_out
    (fixR rfl rfl rfl rfl)

theorem extR1T (v P : ℕ) (hP : 1 ≤ P) (hr : z.rl = .cells (Ruler.rb P) P) (hd : z.d1 = .cells blank 0)
    (hu : z.up1 = .cells (PacketsKeys.Pow.u v) 0) :
    LRuns W (extR (NR := 24) (NO := 29) oD1 oUP1) (extCost v) (roles (toSt z))
      (roles (toSt { z with rl := .cells (Ruler.rb (P + v)) (P + v), d1 := .cells blank (v + 1), up1 := .cells (PacketsKeys.Pow.u v) (v + 1), fl := false })) := by
  refine (extR_run (W := W) (toSt z) oD1 oUP1 (by decide) v P hP hr hd hu).congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (otv z) oD1 _) oUP1 _ = _
  rw [oset_d1, oset_up1]
  rfl

theorem extR1'T (v P : ℕ) (hP : 1 ≤ P) (hr : z.rl = .cells (Ruler.rb P) P) (hd : z.d1' = .cells blank 0)
    (hu : z.up1' = .cells (PacketsKeys.Pow.u v) 0) :
    LRuns W (extR (NR := 24) (NO := 29) oD1' oUP1') (extCost v) (roles (toSt z))
      (roles (toSt { z with rl := .cells (Ruler.rb (P + v)) (P + v), d1' := .cells blank (v + 1), up1' := .cells (PacketsKeys.Pow.u v) (v + 1), fl := false })) := by
  refine (extR_run (W := W) (toSt z) oD1' oUP1' (by decide) v P hP hr hd hu).congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (otv z) oD1' _) oUP1' _ = _
  rw [oset_d1', oset_up1']
  rfl

theorem finishRT (hr : z.rl = .cells (Ruler.rb (W + 1)) (W + 1)) :
    LRuns W (mFinishR (NR := 24) (NO := 29)) (W + 3) (roles (toSt z)) (roles (toSt { z with rl := .ruler })) :=
  (finishR_run (W := W) (toSt z) hr).congr_out (fixR rfl rfl rfl rfl)

theorem loadPT (hr : z.rl = .ruler) (v : ℕ) (hv : v < 2 ^ W) (hd : z.d2 = .cells blank 0)
    (hu : z.up2 = .cells (PacketsKeys.Pow.u v) 0) :
    LRuns W (loadU (NO := 29) rP oD2 oUP2) (loadCost W v) (roles (toSt z))
      (roles (toSt { z with P := v, d2 := .cells blank (v + 1), up2 := .cells (PacketsKeys.Pow.u v) (v + 1), fl := false })) := by
  refine (loadU_run (W := W) (toSt z) hr rP oD2 oUP2 (by decide) v hv hd hu).congr_out (fixR rfl rfl (set_P z v) ?_)
  show Function.update (Function.update (otv z) oD2 _) oUP2 _ = _
  rw [oset_d2, oset_up2]
  rfl

theorem loadST (hr : z.rl = .ruler) (c : Fin 4) (v : ℕ) (hv : v < 2 ^ W) (hd : z.ds c = .cells blank 0)
    (hu : z.us c = .cells (PacketsKeys.Pow.u v) 0) :
    LRuns W (loadU (NO := 29) (rS c) (oDS c) (oUS c)) (loadCost W v) (roles (toSt z))
      (roles (toSt { z with S := Function.update z.S c v, ds := Function.update z.ds c (.cells blank (v + 1)), us := Function.update z.us c (.cells (PacketsKeys.Pow.u v) (v + 1)), fl := false })) := by
  have hdu : (oDS c).val ≠ (oUS c).val := by simp [oDS, oUS]
  refine (loadU_run (W := W) (toSt z) hr (rS c) (oDS c) (oUS c) hdu v hv
    (by show otv z (oDS c) = _; rw [get_ds, hd]) (by show otv z (oUS c) = _; rw [get_us, hu])).congr_out
    (fixR rfl rfl (set_S z v c) ?_)
  show Function.update (Function.update (otv z) (oDS c) _) (oUS c) _ = _
  rw [oset_ds, oset_us]
  rfl

theorem moveJD (hjd : z.jd = .cells blank 0) :
    LRuns W (mMoveR (NR := 24) (NO := 29) oJD) 1 (roles (toSt z)) (roles (toSt { z with jd := .cells blank 1 })) := by
  refine (moveR_run (W := W) (toSt z) oJD blank 0 hjd).congr_out (fixR rfl rfl rfl ?_)
  show Function.update (otv z) oJD _ = _
  rw [oset_jd]

theorem loadJT (hr : z.rl = .ruler) (j : ℕ) (hv : j + 1 < 2 ^ W) (hjd : z.jd = .cells blank 1)
    (hjs : z.js = .cells (sf (List.replicate (j + 1) true)) 1) :
    LRuns W (loadU (NO := 29) rJc oJD oJS) (loadCost W (j + 1)) (roles (toSt z))
      (roles (toSt { z with Jc := j + 1, jd := .cells blank (1 + (j + 1) + 1), js := .cells (sf (List.replicate (j + 1) true)) (1 + (j + 1) + 1), fl := false })) := by
  refine (loadG_run (W := W) (toSt z) hr rJc oJD oJS (by decide) (sf (List.replicate (j + 1) true)) 1 (j + 1)
    (fun i => by rw [PacketsMeta.sf_rep]; apply dec_congr; omega) hv hjd hjs).congr_out (fixR rfl rfl (set_Jc z _) ?_)
  show Function.update (Function.update (otv z) oJD _) oJS _ = _
  rw [oset_jd, oset_js]
  rfl

theorem pow2T (hr : z.rl = .ruler) (hJ : z.Jc < W) :
    LRuns W (pow2 (NO := 29) rJc rE rEp) (pow2Cost W z.Jc) (roles (toSt z))
      (roles (toSt { z with Jc := 0, E := 2 ^ z.Jc, Ep := 2 ^ z.Jc / 2, fl := false })) := by
  refine (pow2_run (W := W) (toSt z) hr rJc rE rEp (by decide) (by decide) (by decide) hJ).congr_out
    (fixR rfl rfl ?_ rfl)
  show Function.update (Function.update (Function.update (rgv z) rJc 0) rE _) rEp _ = _
  rw [set_Jc, set_E, set_Ep]
  rfl

variable (hr : z.rl = .ruler)
include hr

theorem cpyE2mT (h : z.E < 2 ^ W) :
    LRuns W (mCpy (NO := 29) rE2m rE) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with E2m := z.E, fl := false })) :=
  (cpy_run (W := W) (toSt z) hr rE2m rE (by decide) h).congr_out
    (fixR (z' := { z with E2m := z.E, fl := false }) rfl rfl (set_E2m z _) rfl)

theorem decE2mT (h : z.E2m < 2 ^ W) (h1 : 1 ≤ z.E2m) :
    LRuns W (mDec (NO := 29) rE2m) (2 * W + 3) (roles (toSt z))
      (roles (toSt { z with E2m := z.E2m - 1, fl := false })) :=
  (dec_run (W := W) (toSt z) hr rE2m h h1).congr_out
    (fixR (z' := { z with E2m := z.E2m - 1, fl := false }) rfl rfl (set_E2m z _) rfl)

theorem cpyEmT (h : z.Ep < 2 ^ W) :
    LRuns W (mCpy (NO := 29) rEm rEp) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with Em := z.Ep, fl := false })) :=
  (cpy_run (W := W) (toSt z) hr rEm rEp (by decide) h).congr_out
    (fixR (z' := { z with Em := z.Ep, fl := false }) rfl rfl (set_Em z _) rfl)

theorem decEmT (h : z.Em < 2 ^ W) (h1 : 1 ≤ z.Em) :
    LRuns W (mDec (NO := 29) rEm) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with Em := z.Em - 1, fl := false })) :=
  (dec_run (W := W) (toSt z) hr rEm h h1).congr_out
    (fixR (z' := { z with Em := z.Em - 1, fl := false }) rfl rfl (set_Em z _) rfl)

theorem incBT (h : z.B + 1 < 2 ^ W) :
    LRuns W (mInc (NO := 29) rB) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with B := z.B + 1, fl := false })) :=
  (inc_run (W := W) (toSt z) hr rB h).congr_out
    (fixR (z' := { z with B := z.B + 1, fl := false }) rfl rfl (set_B z _) rfl)

theorem incFT (h : z.F + 1 < 2 ^ W) :
    LRuns W (mInc (NO := 29) rF) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with F := z.F + 1, fl := false })) :=
  (inc_run (W := W) (toSt z) hr rF h).congr_out
    (fixR (z' := { z with F := z.F + 1, fl := false }) rfl rfl (set_F z _) rfl)

theorem modBT (hB : z.B < 2 ^ W) (hP : 0 < z.P) (hP2 : 2 * z.P ≤ 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (modP (NO := 29) rB rP rBm rT rMSK) (modCost W) (roles (toSt z))
      (roles (toSt { z with Bm := z.B % z.P, T := 0, MSK := 0, fl := false })) := by
  refine (modP_run (W := W) (toSt z) hr rB rP rBm rT rMSK (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hB hP hP2 hW).congr_out (fixR rfl rfl ?_ rfl)
  show Function.update (Function.update (Function.update (rgv z) rBm _) rT 0) rMSK 0 = _
  rw [set_Bm, set_T, set_MSK]
  rfl

end ProSteps

theorem rewOutT {W : ℕ} (z : TZ) (out : List Bool) (ho : z.os = sS out) (hm : z.om = sM out) :
    LRuns W (mRew (NR := 24) (NO := 29) oOM oOS) (out.length + 1 + 4) (roles (toSt z))
      (roles (toSt { z with om := .cells (sf (List.replicate out.length true)) 1, os := .cells (sf out) 1 })) := by
  refine (rew_run (W := W) (toSt z) oOM oOS (by decide) out.length (out.length + 1) (sf out) (by omega) le_rfl
    (by show otv z oOM = _; rw [show otv z oOM = z.om from rfl, hm])
    (by show otv z oOS = _; rw [show otv z oOS = z.os from rfl, ho])).congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (otv z) oOM _) oOS _ = _
  rw [oset_om, oset_os]

end
end NearCubicWires.PacketsKeys.ThrProg

