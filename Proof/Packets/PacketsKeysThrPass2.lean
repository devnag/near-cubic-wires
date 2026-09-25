import Proof.Packets.PacketsKeysThrPass1

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

/-! ## Register steps used by pass 2 -/

section Regs2
variable {W : ℕ} (z : TZ) (hr : z.rl = .ruler)
include hr

theorem zR : LRuns W (mZero (NO := 29) rR) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with R := 0, fl := false })) :=
  (zero_run (W := W) (toSt z) hr rR).congr_out (fixR (z' := { z with R := 0, fl := false }) rfl rfl (set_R z 0) rfl)
theorem zM : LRuns W (mZero (NO := 29) rM) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with M := 0, fl := false })) :=
  (zero_run (W := W) (toSt z) hr rM).congr_out (fixR (z' := { z with M := 0, fl := false }) rfl rfl (set_M z 0) rfl)
theorem zT : LRuns W (mZero (NO := 29) rT) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with T := 0, fl := false })) :=
  (zero_run (W := W) (toSt z) hr rT).congr_out (fixR (z' := { z with T := 0, fl := false }) rfl rfl (set_T z 0) rfl)
theorem zSG : LRuns W (mZero (NO := 29) rSG) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with SG := 0, fl := false })) :=
  (zero_run (W := W) (toSt z) hr rSG).congr_out (fixR (z' := { z with SG := 0, fl := false }) rfl rfl (set_SG z 0) rfl)

theorem incSG (h : z.SG + 1 < 2 ^ W) :
    LRuns W (mInc (NO := 29) rSG) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with SG := z.SG + 1, fl := false })) :=
  (inc_run (W := W) (toSt z) hr rSG h).congr_out
    (fixR (z' := { z with SG := z.SG + 1, fl := false }) rfl rfl (set_SG z _) rfl)

theorem posSG (h : z.SG < 2 ^ W) :
    LRuns W (mPos (NO := 29) rSG) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with fl := decide (0 < z.SG) })) :=
  (pos_run (W := W) (toSt z) hr rSG h).congr_out (fixR (z' := { z with fl := decide (0 < z.SG) }) rfl rfl rfl rfl)

theorem posR (h : z.R < 2 ^ W) :
    LRuns W (mPos (NO := 29) rR) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with fl := decide (0 < z.R) })) :=
  (pos_run (W := W) (toSt z) hr rR h).congr_out (fixR (z' := { z with fl := decide (0 < z.R) }) rfl rfl rfl rfl)

theorem cpyTP (h : z.P < 2 ^ W) :
    LRuns W (mCpy (NO := 29) rT rP) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with T := z.P, fl := false })) :=
  (cpy_run (W := W) (toSt z) hr rT rP (by decide) h).congr_out
    (fixR (z' := { z with T := z.P, fl := false }) rfl rfl (set_T z _) rfl)

theorem subTR (h1 : z.T < 2 ^ W) (h2 : z.R < 2 ^ W) (h3 : z.R ≤ z.T) :
    LRuns W (mSub (NO := 29) rT rR) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with T := z.T - z.R, fl := false })) :=
  (sub_run (W := W) (toSt z) hr rT rR (by decide) h1 h2 h3).congr_out
    (fixR (z' := { z with T := z.T - z.R, fl := false }) rfl rfl (set_T z _) rfl)

theorem cpyRT (h : z.T < 2 ^ W) :
    LRuns W (mCpy (NO := 29) rR rT) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with R := z.T, fl := false })) :=
  (cpy_run (W := W) (toSt z) hr rR rT (by decide) h).congr_out
    (fixR (z' := { z with R := z.T, fl := false }) rfl rfl (set_R z _) rfl)

theorem clrR (h : z.R < 2 ^ W) :
    LRuns W (mClr (NO := 29) rR) (2 * W + 3) (roles (toSt z)) (roles (toSt { z with fl := false })) :=
  (clr_run (W := W) (toSt z) hr rR h).congr_out (fixR (z' := { z with fl := false }) rfl rfl rfl rfl)

theorem modXR (hX : z.X < 2 ^ W) (hP : 0 < z.P) (hP2 : 2 * z.P ≤ 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (modP (NO := 29) rX rP rR rT rMSK) (modCost W) (roles (toSt z))
      (roles (toSt { z with R := z.X % z.P, T := 0, MSK := 0, fl := false })) := by
  refine (modP_run (W := W) (toSt z) hr rX rP rR rT rMSK (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hX hP hP2 hW).congr_out (fixR rfl rfl ?_ rfl)
  show Function.update (Function.update (Function.update (rgv z) rR _) rT 0) rMSK 0 = _
  rw [set_R, set_T, set_MSK]
  rfl

theorem modMR (hM : z.M < 2 ^ W) (hP : 0 < z.P) (hP2 : 2 * z.P ≤ 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (modP (NO := 29) rM rP rR rT rMSK) (modCost W) (roles (toSt z))
      (roles (toSt { z with R := z.M % z.P, T := 0, MSK := 0, fl := false })) := by
  refine (modP_run (W := W) (toSt z) hr rM rP rR rT rMSK (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hM hP hP2 hW).congr_out (fixR rfl rfl ?_ rfl)
  show Function.update (Function.update (Function.update (rgv z) rR _) rT 0) rMSK 0 = _
  rw [set_R, set_T, set_MSK]
  rfl

theorem modMF (hM : z.M < 2 ^ W) (hP : 0 < z.P) (hP2 : 2 * z.P ≤ 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (modP (NO := 29) rM rP rF rT rMSK) (modCost W) (roles (toSt z))
      (roles (toSt { z with F := z.M % z.P, T := 0, MSK := 0, fl := false })) := by
  refine (modP_run (W := W) (toSt z) hr rM rP rF rT rMSK (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hM hP hP2 hW).congr_out (fixR rfl rfl ?_ rfl)
  show Function.update (Function.update (Function.update (rgv z) rF _) rT 0) rMSK 0 = _
  rw [set_F, set_T, set_MSK]
  rfl

theorem mulFR (hy : z.R < 2 ^ W) (hxy : z.F * z.R < 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (mMul (NO := 29) rF rR rM rMT rMM) (13 * W * W + 60 * W + 40) (roles (toSt z))
      (roles (toSt { z with M := z.F * z.R, MT := 0, MM := 0, fl := false })) := by
  refine (mul_run (W := W) (toSt z) hr rF rR rM rMT rMM (by decide) hy hxy hW).congr_out (fixR rfl rfl ?_ rfl)
  show Function.update (Function.update (Function.update (rgv z) rM _) rMT 0) rMM 0 = _
  rw [set_M, set_MT, set_MM]
  rfl

theorem mulFBm (hy : z.Bm < 2 ^ W) (hxy : z.F * z.Bm < 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (mMul (NO := 29) rF rBm rM rMT rMM) (13 * W * W + 60 * W + 40) (roles (toSt z))
      (roles (toSt { z with M := z.F * z.Bm, MT := 0, MM := 0, fl := false })) := by
  refine (mul_run (W := W) (toSt z) hr rF rBm rM rMT rMM (by decide) hy hxy hW).congr_out (fixR rfl rfl ?_ rfl)
  show Function.update (Function.update (Function.update (rgv z) rM _) rMT 0) rMM 0 = _
  rw [set_M, set_MT, set_MM]
  rfl

theorem testTZ (j : ℕ) (hE : z.E = 2 ^ (j + 1)) (hE2m : z.E2m = 2 ^ (j + 1) - 1) (hEm : z.Em = 2 ^ j - 1)
    (hR : z.R < 2 ^ W) (hRB : z.R ≤ z.P) (hEW : 2 ^ (j + 1) < 2 ^ W) :
    LRuns W (testB (NO := 29) rR rE rE2m rEm rT) (testCost W z.P) (roles (toSt z))
      (roles (toSt { z with T := z.R % 2 ^ (j + 1), fl := z.R.testBit j })) := by
  refine (testB_run (W := W) (toSt z) hr rR rE rE2m rEm rT (by decide) (by decide) (by decide) (by decide) j z.P
    hE hE2m hEm hR hRB hEW).congr_out (fixR rfl rfl ?_ rfl)
  show Function.update (rgv z) rT _ = _
  rw [set_T]
  rfl

end Regs2

theorem appOut {W : ℕ} (z : TZ) (b : Bool) (out : List Bool) (ho : z.os = sS out) (hm : z.om = sM out) :
    LRuns W (mApp (NR := 24) (NO := 29) b oOS oOM) 1 (roles (toSt z))
      (roles (toSt { z with os := sS (out ++ [b]), om := sM (out ++ [b]) })) := by
  refine (app_run (W := W) (toSt z) b oOS oOM (by decide) out ho hm).congr_out (fixR rfl rfl rfl ?_)
  show Function.update (Function.update (otv z) oOS _) oOM _ = _
  rw [oset_os, oset_om]

/-! ## One weight -/

/-- The residue with the sign fixed: `(w mod P).toNat` from the sign and `|w| mod P`. -/
def sfix (neg : Bool) (P R1 : ℕ) : ℕ := if neg = true ∧ 0 < R1 then P - R1 else R1

theorem sfix_eq (w : ℤ) (P : ℕ) (hP : 0 < P) : sfix (decide (w < 0)) P (w.natAbs % P) = (w % (P : ℤ)).toNat := by
  unfold sfix
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · have h1 : ¬ ((n : ℤ) < 0) := by omega
    simp only [h1, decide_false, Bool.false_eq_true, false_and, if_false, Int.natAbs_natCast]
    rw [← Int.natCast_mod, Int.toNat_natCast]
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · have h1 : (-(n : ℤ)) < 0 := by omega
      simp only [h1, decide_true, true_and, Int.natAbs_neg, Int.natAbs_natCast]
      rw [Int.neg_emod]
      by_cases hd : P ∣ n
      · have hm : n % P = 0 := Nat.mod_eq_zero_of_dvd hd
        rw [if_neg (by omega), if_pos (by exact_mod_cast hd), hm]
        simp
      · have hm : 0 < n % P := Nat.pos_of_ne_zero (fun h => hd (Nat.dvd_of_mod_eq_zero h))
        rw [if_pos hm, if_neg (by exact_mod_cast hd)]
        have hlt : n % P < P := Nat.mod_lt _ hP
        rw [Int.natAbs_natCast, ← Int.natCast_mod]
        omega

/-- The bit emitted for weight `w`. -/
def wb (F P j : ℕ) (w : ℤ) : Bool := ((F * (w % (P : ℤ)).toNat) % P).testBit j

abbrev nopT := nop (4 + 24 + 29)

def sgRec := Ite nopT (mInc (NO := 29) rSG) nopT FL

def fixSeq :=
  Composition.machine (mCpy (NO := 29) rT rP) (Composition.machine (mSub (NO := 29) rT rR)
    (Composition.machine (mCpy (NO := 29) rR rT) (mZero (NO := 29) rT)))

def signFix := Ite (mPos (NO := 29) rSG) (Ite (mPos (NO := 29) rR) fixSeq (mClr (NO := 29) rR) FL) (mClr (NO := 29) rR) FL

def emitB := Ite nopT (mApp (NR := 24) (NO := 29) true oOS oOM) (mApp (NR := 24) (NO := 29) false oOS oOM) FL

def cleanW :=
  Composition.machine (mZero (NO := 29) rX) (Composition.machine (mZero (NO := 29) rR)
    (Composition.machine (mZero (NO := 29) rM) (Composition.machine (mZero (NO := 29) rT)
      (Composition.machine (mZero (NO := 29) rSG) (mDec (NO := 29) rI)))))

def wBody (c : Fin 4) :=
  Composition.machine (rdInt c) (Composition.machine sgRec (Composition.machine (modP (NO := 29) rX rP rR rT rMSK)
    (Composition.machine signFix (Composition.machine (mMul (NO := 29) rF rR rM rMT rMM)
      (Composition.machine (modP (NO := 29) rM rP rR rT rMSK) (Composition.machine (testB (NO := 29) rR rE rE2m rEm rT)
        (Composition.machine emitB cleanW)))))))

def fixCost (W : ℕ) : ℕ :=
  (2 * W + 3) + ((2 * W + 3) + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3)))) + (2 * W + 3) + 2) +
    (2 * W + 3) + 2

def cleanCost (W : ℕ) : ℕ :=
  (2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3)))))

def wBodyCost (W Pb : ℕ) : ℕ :=
  (1 + 1 + (3 * W + 5)) + 1 + ((0 + (2 * W + 3) + 0 + 2) + 1 + (modCost W + 1 + (fixCost W + 1 +
    ((13 * W * W + 60 * W + 40) + 1 + (modCost W + 1 + (testCost W Pb + 1 + ((0 + 1 + 1 + 2) + 1 + cleanCost W)))))))

/-- The states of pass 2. -/
def w2 (z : TZ) (cc : Fin 8 → TS) (I X R M T MSK MT MM SG : ℕ) (out : List Bool) (f : Bool) : TZ := { z with cc := cc, I := I, X := X, R := R, M := M, T := T, MSK := MSK, MT := MT, MM := MM, SG := SG, os := sS out, om := sM out, fl := f }

theorem natAbs_lt_pay (w : ℤ) (pre post pay : List Bool) (hpay : pay = pre ++ intWord w ++ post) {W : ℕ}
    (hW : pay.length ≤ W) : w.natAbs < 2 ^ W := by
  have h1 : w.natAbs < 2 ^ (natWord w.natAbs).length :=
    lt_of_lt_of_le (ReadNat.lt_natBitLength _) (Nat.pow_le_pow_right (by norm_num) (natBitLength_le_len _))
  have h2 : (natWord w.natAbs).length ≤ pay.length := by rw [hpay]; simp [intWord]; omega
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))

section WBody
variable {W : ℕ} (z0 : TZ) (hr : z0.rl = .ruler) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool)
include hr

theorem wBody_run (q : ℕ) (w : ℤ) (pre post : List Bool) (hpay : pay = pre ++ intWord w ++ post)
    (hq : q = pre.length + 1) (I : ℕ) (hI : 1 ≤ I) (hIW : I < 2 ^ W) (out : List Bool) (j : ℕ)
    (hE : z0.E = 2 ^ (j + 1)) (hE2m : z0.E2m = 2 ^ (j + 1) - 1) (hEm : z0.Em = 2 ^ j - 1)
    (hP : 0 < z0.P) (hP2 : 2 * z0.P ≤ 2 ^ W) (hPP : z0.P * z0.P < 2 ^ W) (hF : z0.F < z0.P)
    (hEW : 2 ^ (j + 1) < 2 ^ W) (hW1 : 1 ≤ W) (hW : pay.length ≤ W) :
    LRuns W (wBody c) (wBodyCost W z0.P)
      (roles (toSt (w2 z0 (strm base c pay q) I 0 0 0 0 0 0 0 0 out true)))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) (I - 1) 0 0 0 0 0 0 0 0
        (out ++ [wb z0.F z0.P j w]) false))) := by
  have hwW := natAbs_lt_pay w pre post pay hpay hW
  have hPW : z0.P < 2 ^ W := by omega
  -- the sign and the magnitude
  have e1 : LRuns W (rdInt c) (1 + 1 + (3 * W + 5)) (roles (toSt (w2 z0 (strm base c pay q) I 0 0 0 0 0 0 0 0 out true)))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs 0 0 0 0 0 0 0 out (decide (w < 0))))) :=
    rdInt_run (W := W) (w2 z0 (strm base c pay q) I 0 0 0 0 0 0 0 0 out true) hr base c pay q w pre post hpay hq rfl hW
  -- the sign register
  have e2 : LRuns W sgRec (0 + (2 * W + 3) + 0 + 2)
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs 0 0 0 0 0 0 0 out (decide (w < 0)))))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs 0 0 0 0 0 0 (decide (w < 0)).toNat
        out false))) := by
    unfold sgRec
    refine Ite.runs (W := W) (np := 2 * W + 3) (nq := 0) nopT (mInc (NO := 29) rSG) nopT FL (decide (w < 0))
      (nop_lruns (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs 0 0 0 0 0 0 0 out
        (decide (w < 0)))))) rfl ?_ ?_
    · intro hb
      have h := incSG (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs 0 0 0 0 0 0 0 out
        (decide (w < 0))) hr (by show 0 + 1 < 2 ^ W; omega)
      rw [hb] at h ⊢
      exact h
    · intro hb
      rw [hb]
      exact nop_lruns _
  -- `R := |w| mod P`
  have e3 : LRuns W (modP (NO := 29) rX rP rR rT rMSK) (modCost W)
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs 0 0 0 0 0 0 (decide (w < 0)).toNat
        out false)))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0 0 0 0 0
        (decide (w < 0)).toNat out false))) :=
    modXR (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs 0 0 0 0 0 0 (decide (w < 0)).toNat
      out false) hr hwW hP hP2 hW1
  -- the sign fix
  have hR1 : w.natAbs % z0.P < z0.P := Nat.mod_lt _ hP
  have e4 : LRuns W signFix (fixCost W)
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0 0 0 0 0
        (decide (w < 0)).toNat out false)))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs
        (sfix (decide (w < 0)) z0.P (w.natAbs % z0.P)) 0 0 0 0 0 (decide (w < 0)).toNat out false))) := by
    have hsg : (decide (w < 0)).toNat < 2 ^ W := by
      have : (decide (w < 0)).toNat ≤ 1 := by cases decide (w < 0) <;> simp
      have : 1 < 2 ^ W := Nat.one_lt_two_pow_iff.mpr (by omega)
      omega
    unfold signFix
    refine Ite.runs (W := W) (mPos (NO := 29) rSG) (Ite (mPos (NO := 29) rR) fixSeq (mClr (NO := 29) rR) FL)
      (mClr (NO := 29) rR) FL (decide (0 < (decide (w < 0)).toNat))
      (posSG (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0 0 0 0 0
        (decide (w < 0)).toNat out false) hr hsg) rfl ?_ ?_
    · intro hb
      have hneg : decide (w < 0) = true := by
        cases h : decide (w < 0)
        · rw [h] at hb; simp at hb
        · rfl
      refine Ite.runs (W := W) (mPos (NO := 29) rR) fixSeq (mClr (NO := 29) rR) FL (decide (0 < w.natAbs % z0.P))
        (posR (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0 0 0 0 0
          (decide (w < 0)).toNat out (decide (0 < (decide (w < 0)).toNat))) hr
          (by show w.natAbs % z0.P < 2 ^ W; omega)) rfl ?_ ?_
      · intro hp
        have hp' : 0 < w.natAbs % z0.P := by simpa using hp
        have f1 := cpyTP (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0 0 0
          0 0 (decide (w < 0)).toNat out (decide (0 < w.natAbs % z0.P))) hr hPW
        have f2 := subTR (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0
          z0.P 0 0 0 (decide (w < 0)).toNat out false) hr hPW (by show w.natAbs % z0.P < 2 ^ W; omega)
          (by show w.natAbs % z0.P ≤ z0.P; omega)
        have f3 := cpyRT (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0
          (z0.P - w.natAbs % z0.P) 0 0 0 (decide (w < 0)).toNat out false) hr (by show z0.P - _ < 2 ^ W; omega)
        have f4 := zT (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.P - w.natAbs % z0.P) 0
          (z0.P - w.natAbs % z0.P) 0 0 0 (decide (w < 0)).toNat out false) hr
        have hs : sfix (decide (w < 0)) z0.P (w.natAbs % z0.P) = z0.P - w.natAbs % z0.P := by
          unfold sfix; rw [if_pos ⟨hneg, hp'⟩]
        rw [hs]
        exact f1.seq (f2.seq (f3.seq f4))
      · intro hp
        have hp' : ¬ 0 < w.natAbs % z0.P := by simpa using hp
        have hs : sfix (decide (w < 0)) z0.P (w.natAbs % z0.P) = w.natAbs % z0.P := by
          unfold sfix; rw [if_neg (fun h => hp' h.2)]
        rw [hs]
        exact clrR (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0 0 0 0 0
          (decide (w < 0)).toNat out (decide (0 < w.natAbs % z0.P))) hr (by show w.natAbs % z0.P < 2 ^ W; omega)
    · intro hb
      have hpos : decide (w < 0) = false := by
        cases h : decide (w < 0)
        · rfl
        · rw [h] at hb; simp at hb
      have hs : sfix (decide (w < 0)) z0.P (w.natAbs % z0.P) = w.natAbs % z0.P := by
        unfold sfix; rw [hpos]; simp
      rw [hs]
      exact clrR (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (w.natAbs % z0.P) 0 0 0 0 0
        (decide (w < 0)).toNat out (decide (0 < (decide (w < 0)).toNat))) hr (by show w.natAbs % z0.P < 2 ^ W; omega)
  -- `M := F·R`, `R := M mod P`
  have hR2 : sfix (decide (w < 0)) z0.P (w.natAbs % z0.P) < z0.P := by
    unfold sfix; split_ifs <;> omega
  set R2 := sfix (decide (w < 0)) z0.P (w.natAbs % z0.P) with hR2d
  have hFR : z0.F * R2 < 2 ^ W := lt_of_le_of_lt (Nat.mul_le_mul hF.le hR2.le) hPP
  have e5 : LRuns W (mMul (NO := 29) rF rR rM rMT rMM) (13 * W * W + 60 * W + 40)
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs R2 0 0 0 0 0 (decide (w < 0)).toNat
        out false)))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs R2 (z0.F * R2) 0 0 0 0
        (decide (w < 0)).toNat out false))) :=
    mulFR (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs R2 0 0 0 0 0 (decide (w < 0)).toNat
      out false) hr (by show R2 < 2 ^ W; omega) hFR hW1
  have e6 : LRuns W (modP (NO := 29) rM rP rR rT rMSK) (modCost W)
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs R2 (z0.F * R2) 0 0 0 0
        (decide (w < 0)).toNat out false)))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P) (z0.F * R2) 0 0 0 0
        (decide (w < 0)).toNat out false))) :=
    modMR (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs R2 (z0.F * R2) 0 0 0 0
      (decide (w < 0)).toNat out false) hr hFR hP hP2 hW1
  -- the bit
  have hR3 : z0.F * R2 % z0.P < z0.P := Nat.mod_lt _ hP
  have e7 : LRuns W (testB (NO := 29) rR rE rE2m rEm rT) (testCost W z0.P)
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P) (z0.F * R2) 0 0 0 0
        (decide (w < 0)).toNat out false)))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P) (z0.F * R2)
        (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat out ((z0.F * R2 % z0.P).testBit j)))) :=
    testTZ (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P) (z0.F * R2) 0 0 0 0
      (decide (w < 0)).toNat out false) hr j hE hE2m hEm (by show z0.F * R2 % z0.P < 2 ^ W; omega)
      (by show z0.F * R2 % z0.P ≤ z0.P; omega) hEW
  -- append the bit
  set b := (z0.F * R2 % z0.P).testBit j with hbd
  have e8 : LRuns W emitB (0 + 1 + 1 + 2)
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P) (z0.F * R2)
        (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat out b)))
      (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P) (z0.F * R2)
        (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat (out ++ [b]) b))) := by
    unfold emitB
    refine Ite.runs (W := W) (np := 1) (nq := 1) nopT (mApp (NR := 24) (NO := 29) true oOS oOM)
      (mApp (NR := 24) (NO := 29) false oOS oOM)
      FL b (nop_lruns (roles (toSt (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P)
        (z0.F * R2) (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat out b)))) rfl ?_ ?_
    · intro hb
      have h := appOut (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P)
        (z0.F * R2) (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat out b) true out rfl rfl
      rw [hb] at h ⊢
      exact h
    · intro hb
      have h := appOut (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P)
        (z0.F * R2) (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat out b) false out rfl rfl
      rw [hb] at h ⊢
      exact h
  -- clear the scratch
  have g1 := zX (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I w.natAbs (z0.F * R2 % z0.P) (z0.F * R2)
    (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat (out ++ [b]) b) hr
  have g2 := zR (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I 0 (z0.F * R2 % z0.P) (z0.F * R2)
    (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat (out ++ [b]) false) hr
  have g3 := zM (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I 0 0 (z0.F * R2)
    (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat (out ++ [b]) false) hr
  have g4 := zT (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I 0 0 0
    (z0.F * R2 % z0.P % 2 ^ (j + 1)) 0 0 0 (decide (w < 0)).toNat (out ++ [b]) false) hr
  have g5 := zSG (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I 0 0 0 0 0 0 0 (decide (w < 0)).toNat
    (out ++ [b]) false) hr
  have g6 := decI (W := W) (w2 z0 (strm base c pay (q + (intWord w).length)) I 0 0 0 0 0 0 0 0 (out ++ [b]) false) hr
    hIW hI
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq
    (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq g6))))))))))))
  have hbw : b = wb z0.F z0.P j w := by
    rw [hbd, hR2d, sfix_eq w z0.P hP]
    rfl
  rw [hbw] at hall
  exact hall

end WBody

/-! ## The weight loop -/

def wLoop (c : Fin 4) := Loop (mPos (NO := 29) rI) (wBody c) FL

section WLoop
variable {W : ℕ} (z0 : TZ) (hr : z0.rl = .ruler) (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool)
include hr

theorem wLoop_run (zl : List ℤ) (pre0 post0 : List Bool) (hpay : pay = pre0 ++ zl.flatMap intWord ++ post0)
    (hIW : zl.length < 2 ^ W) (out0 : List Bool) (j : ℕ)
    (hE : z0.E = 2 ^ (j + 1)) (hE2m : z0.E2m = 2 ^ (j + 1) - 1) (hEm : z0.Em = 2 ^ j - 1)
    (hP : 0 < z0.P) (hP2 : 2 * z0.P ≤ 2 ^ W) (hPP : z0.P * z0.P < 2 ^ W) (hF : z0.F < z0.P)
    (hEW : 2 ^ (j + 1) < 2 ^ W) (hW1 : 1 ≤ W) (hW : pay.length ≤ W) :
    LRuns W (wLoop c) ((zl.length + 1) * ((2 * W + 3) + wBodyCost W z0.P + 2))
      (roles (toSt (w2 z0 (strm base c pay (pre0.length + 1)) zl.length 0 0 0 0 0 0 0 0 out0 false)))
      (roles (toSt (w2 z0 (strm base c pay (pre0.length + 1 + (zl.flatMap intWord).length)) 0 0 0 0 0 0 0 0 0
        (out0 ++ zl.map (wb z0.F z0.P j)) false))) := by
  have hl := Loop.runs (W := W) (mPos (NO := 29) rI) (wBody c) FL
    (fun i => roles (toSt (w2 z0 (strm base c pay (pre0.length + 1 + ((zl.take i).flatMap intWord).length))
      (zl.length - i) 0 0 0 0 0 0 0 0 (out0 ++ (zl.take i).map (wb z0.F z0.P j)) false)))
    (fun i => roles (toSt (w2 z0 (strm base c pay (pre0.length + 1 + ((zl.take i).flatMap intWord).length))
      (zl.length - i) 0 0 0 0 0 0 0 0 (out0 ++ (zl.take i).map (wb z0.F z0.P j)) (decide (i < zl.length))))) zl.length
    (fun i hi => by
      have h := posI (W := W) (w2 z0 (strm base c pay (pre0.length + 1 + ((zl.take i).flatMap intWord).length))
        (zl.length - i) 0 0 0 0 0 0 0 0 (out0 ++ (zl.take i).map (wb z0.F z0.P j)) false) hr
        (by show zl.length - i < 2 ^ W; omega)
      refine h.congr_out (congrArg (fun f => roles (toSt { w2 z0 (strm base c pay (pre0.length + 1 +
        ((zl.take i).flatMap intWord).length)) (zl.length - i) 0 0 0 0 0 0 0 0
        (out0 ++ (zl.take i).map (wb z0.F z0.P j)) false with fl := f })) ?_)
      show decide (0 < zl.length - i) = decide (i < zl.length)
      apply dec_congr; omega)
    (fun i _ => rfl)
    (fun i hi => by
      have hb := wBody_run (W := W) z0 hr base c pay (pre0.length + 1 + ((zl.take i).flatMap intWord).length) zl[i]
        (pre0 ++ (zl.take i).flatMap intWord) ((zl.drop (i + 1)).flatMap intWord ++ post0)
        (by rw [hpay, flatMap_split zl i hi]; simp [List.append_assoc]) (by simp; omega) (zl.length - i)
        (by omega) (by omega) (out0 ++ (zl.take i).map (wb z0.F z0.P j)) j hE hE2m hEm hP hP2 hPP hF hEW hW1 hW
      have h1 : decide (i < zl.length) = true := by simp [hi]
      rw [h1]
      have hq : pre0.length + 1 + ((zl.take i).flatMap intWord).length + (intWord zl[i]).length =
          pre0.length + 1 + ((zl.take (i + 1)).flatMap intWord).length := by
        rw [flatMap_take_succ zl i hi]; omega
      have hout : out0 ++ (zl.take i).map (wb z0.F z0.P j) ++ [wb z0.F z0.P j zl[i]] =
          out0 ++ (zl.take (i + 1)).map (wb z0.F z0.P j) := by
        rw [List.take_succ_eq_append_getElem hi, List.map_append, List.map_singleton, List.append_assoc]
      have hI : zl.length - i - 1 = zl.length - (i + 1) := by omega
      refine hb.congr_out ?_
      rw [hq, hout, hI])
  have hsrc : roles (toSt (w2 z0 (strm base c pay (pre0.length + 1 + ((zl.take 0).flatMap intWord).length))
      (zl.length - 0) 0 0 0 0 0 0 0 0 (out0 ++ (zl.take 0).map (wb z0.F z0.P j)) false)) =
      roles (toSt (w2 z0 (strm base c pay (pre0.length + 1)) zl.length 0 0 0 0 0 0 0 0 out0 false)) := by
    simp
  have htgt : roles (toSt (w2 z0 (strm base c pay (pre0.length + 1 + ((zl.take zl.length).flatMap intWord).length))
      (zl.length - zl.length) 0 0 0 0 0 0 0 0 (out0 ++ (zl.take zl.length).map (wb z0.F z0.P j))
      (decide (zl.length < zl.length)))) =
      roles (toSt (w2 z0 (strm base c pay (pre0.length + 1 + (zl.flatMap intWord).length)) 0 0 0 0 0 0 0 0 0
        (out0 ++ zl.map (wb z0.F z0.P j)) false)) := by
    rw [List.take_length, Nat.sub_self]
    simp
  exact PacketsKeys.lr_src (hl.congr_out htgt) hsrc

end WLoop

/-! ## Pass-2 body: one circuit -/

def p2Body (c : Fin 4) :=
  Composition.machine (seek c) (Composition.machine (mCpy (NO := 29) rI rA) (Composition.machine (wLoop c)
    (Composition.machine (mZero (NO := 29) rA) (Composition.machine (mMul (NO := 29) rF rBm rM rMT rMM)
      (Composition.machine (modP (NO := 29) rM rP rF rT rMSK) (mZero (NO := 29) rM))))))

def p2BodyCost (W A s P : ℕ) : ℕ :=
  seekCost W A s + 1 + ((2 * W + 3) + 1 + ((A + 1) * ((2 * W + 3) + wBodyCost W P + 2) + 1 + ((2 * W + 3) + 1 +
    ((13 * W * W + 60 * W + 40) + 1 + (modCost W + 1 + (2 * W + 3))))))

/-- The pass-2 states: the fields pass 2 changes, over a base state. -/
def p2S (z : TZ) (cc : Fin 8 → TS) (A K I X F R M T MSK MT MM SG : ℕ) (out : List Bool) (f : Bool) : TZ := { z with cc := cc, A := A, K := K, I := I, X := X, F := F, R := R, M := M, T := T, MSK := MSK, MT := MT, MM := MM, SG := SG, os := sS out, om := sM out, fl := f }

theorem strm_self (base : Fin 8 → TS) (c : Fin 4) (pay : List Bool) (h1 : base (cs c) = .cells (sf pay) 1)
    (h2 : base (cm c) = .cells (mks pay) 1) : strm base c pay 1 = base := by
  funext k
  unfold strm
  simp only [Function.update_apply]
  split_ifs with ha hb
  · rw [ha]; exact h2.symm
  · rw [hb]; exact h1.symm
  · rfl

section Body2
variable {W : ℕ} (z : TZ) (hr : z.rl = .ruler) (c : Fin 4)
include hr

theorem p2Body_run (pay : List Bool) {A : ℕ} (gs : List (ExactThresholdGate A)) (out : List Bool) (j : ℕ)
    (hpay : pay = natWord A ++ natWord gs.length ++ gs.flatMap exactWord)
    (hcs : z.cc (cs c) = .cells (sf pay) 1) (hcm : z.cc (cm c) = .cells (mks pay) 1)
    (hsel : z.S c < gs.length) (hW : pay.length ≤ W) (hAW : A + 2 < 2 ^ W) (hgW : gs.length < 2 ^ W)
    (hE : z.E = 2 ^ (j + 1)) (hE2m : z.E2m = 2 ^ (j + 1) - 1) (hEm : z.Em = 2 ^ j - 1)
    (hP : 0 < z.P) (hP2 : 2 * z.P ≤ 2 ^ W) (hPP : z.P * z.P < 2 ^ W) (hF : z.F < z.P) (hBm : z.Bm < z.P)
    (hEW : 2 ^ (j + 1) < 2 ^ W) (hW1 : 1 ≤ W) :
    LRuns W (p2Body c) (p2BodyCost W A (z.S c) z.P)
      (roles (toSt (p2S z z.cc 0 0 0 0 z.F 0 0 0 0 0 0 0 out true)))
      (roles (toSt (p2S z (strm z.cc c pay ((natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length
        + 1 + ((List.ofFn (gs[z.S c]'hsel).weight).flatMap intWord).length)) 0 (z.S c - z.S c) 0 0
        (z.F * z.Bm % z.P) 0 0 0 0 0 0 0 (out ++ (List.ofFn (gs[z.S c]'hsel).weight).map (wb z.F z.P j)) false))) := by
  have hself : strm z.cc c pay 1 = z.cc := strm_self z.cc c pay hcs hcm
  -- seek
  have e1 : LRuns W (seek c) (seekCost W A (z.S c)) (roles (toSt (p2S z z.cc 0 0 0 0 z.F 0 0 0 0 0 0 0 out true)))
      (roles (toSt (p2S z (strm z.cc c pay ((natWord A ++ natWord gs.length).length + 1 +
        ((gs.take (z.S c)).flatMap exactWord).length)) A (z.S c - z.S c) 0 0 z.F 0 0 0 0 0 0 0 out false))) :=
    seek_run (W := W) (p2S z z.cc 0 0 0 0 z.F 0 0 0 0 0 0 0 out true) hr z.cc c pay gs hself.symm hpay rfl hsel.le hW
      hAW hgW
  have e2 := cpyIA (W := W) (p2S z (strm z.cc c pay ((natWord A ++ natWord gs.length).length + 1 +
    ((gs.take (z.S c)).flatMap exactWord).length)) A (z.S c - z.S c) 0 0 z.F 0 0 0 0 0 0 0 out false) hr
    (by show A < 2 ^ W; omega)
  -- the weights
  set g := gs[z.S c]'hsel with hg
  have hzl : (List.ofFn g.weight).length = A := by simp
  have hpay1 : pay = (natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord) ++
      (List.ofFn g.weight).flatMap intWord ++ (intWord g.target ++ (gs.drop (z.S c + 1)).flatMap exactWord) := by
    rw [hpay, exact_split gs (z.S c) hsel]
    simp [zs, List.flatMap_append, List.append_assoc, hg]
  have e3 := wLoop_run (W := W) (p2S z (strm z.cc c pay 1) A (z.S c - z.S c) 0 0 z.F 0 0 0 0 0 0 0 out false) hr
    z.cc c pay (List.ofFn g.weight) (natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord)
    (intWord g.target ++ (gs.drop (z.S c + 1)).flatMap exactWord) hpay1 (by rw [hzl]; omega) out j hE hE2m hEm hP
    hP2 hPP hF hEW hW1 hW
  have b23 : roles (toSt { p2S z (strm z.cc c pay ((natWord A ++ natWord gs.length).length + 1 +
      ((gs.take (z.S c)).flatMap exactWord).length)) A (z.S c - z.S c) 0 0 z.F 0 0 0 0 0 0 0 out false with
        I := A, fl := false }) =
      roles (toSt (w2 (p2S z (strm z.cc c pay 1) A (z.S c - z.S c) 0 0 z.F 0 0 0 0 0 0 0 out false)
        (strm z.cc c pay ((natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1))
        (List.ofFn g.weight).length 0 0 0 0 0 0 0 0 out false)) := by
    rw [hzl]
    have hq : (natWord A ++ natWord gs.length).length + 1 + ((gs.take (z.S c)).flatMap exactWord).length =
        (natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1 := by simp; omega
    rw [hq]
    rfl
  have e2' := e2.congr_out b23
  set qE := (natWord A ++ natWord gs.length ++ (gs.take (z.S c)).flatMap exactWord).length + 1 +
    ((List.ofFn g.weight).flatMap intWord).length with hqE
  set bits := (List.ofFn g.weight).map (wb z.F z.P j) with hbits
  have e4 := zA (W := W) (w2 (p2S z (strm z.cc c pay 1) A (z.S c - z.S c) 0 0 z.F 0 0 0 0 0 0 0 out false)
    (strm z.cc c pay qE) 0 0 0 0 0 0 0 0 0 (out ++ bits) false) hr
  have e5 := mulFBm (W := W) (p2S z (strm z.cc c pay qE) 0 (z.S c - z.S c) 0 0 z.F 0 0 0 0 0 0 0 (out ++ bits) false) hr
    (by show z.Bm < 2 ^ W; omega)
    (by show z.F * z.Bm < 2 ^ W; exact lt_of_le_of_lt (Nat.mul_le_mul hF.le hBm.le) hPP) hW1
  have e6 := modMF (W := W) (p2S z (strm z.cc c pay qE) 0 (z.S c - z.S c) 0 0 z.F 0 (z.F * z.Bm) 0 0 0 0 0 (out ++ bits)
    false) hr (by show z.F * z.Bm < 2 ^ W; exact lt_of_le_of_lt (Nat.mul_le_mul hF.le hBm.le) hPP) hP hP2 hW1
  have e7 := zM (W := W) (p2S z (strm z.cc c pay qE) 0 (z.S c - z.S c) 0 0 (z.F * z.Bm % z.P) 0 (z.F * z.Bm) 0 0 0 0 0
    (out ++ bits) false) hr
  refine (e1.seq (e2'.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).enlarge ?_
  unfold p2BodyCost
  rw [hzl]
  exact le_rfl

end Body2

end
end NearCubicWires.PacketsKeys.ThrProg

