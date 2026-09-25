import Proof.Packets.PacketsKeysRM

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsKeys.RM
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsMeta NearCubicWires.PacketsSymBits NearCubicWires.RepairRepresentation
noncomputable section

section Ruler
variable {NR NO : ℕ}

def mRuleR := RecoveryFocus.machine ![(RL : Fin (4 + NR + NO))] moveR
def mMarkR := RecoveryFocus.machine ![(RL : Fin (4 + NR + NO))] PacketsKeys.Pow.markR
def mFinishR := RecoveryFocus.machine ![(RL : Fin (4 + NR + NO))] Ruler.finish
def mAppendR (k : ℕ) (mk sm : Fin NO) := RecoveryFocus.machine ![(os mk : Fin (4 + NR + NO)), os sm, RL] (Ruler.append k)

variable {W : ℕ} (s : St NR NO)

theorem ruleR_run (hr : s.rl = .cells blank 0) :
    LRuns W (mRuleR (NR := NR) (NO := NO)) 1 (roles s) (roles { s with rl := .cells (Ruler.rb 1) 1 }) := by
  have hh := (moveR_lruns W 0 blank).dockK ![(RL : Fin (4 + NR + NO))] (fun i j _ => Subsingleton.elim i j) (roles s)
    (by intro j; fin_cases j; exact (roles_RL s).trans hr) [0] (by intro j hj; fin_cases j; simp at hj)
  have e : ([0] : List (Fin 1)).foldr (fun j ρ => Function.update ρ
      ((![(RL : Fin (4 + NR + NO))] : Fin 1 → Fin (4 + NR + NO)) j) ((![.cells blank (0 + 1)] : Fin 1 → TS) j))
      (roles s) = Function.update (roles s) RL (.cells blank 1) := rfl
  rw [e, upd_RL, ← PacketsKeys.Setup.rb_one] at hh
  exact hh

theorem markR_run (P : ℕ) (hP : 1 ≤ P) (hr : s.rl = .cells (Ruler.rb P) P) :
    LRuns W (mMarkR (NR := NR) (NO := NO)) 1 (roles s) (roles { s with rl := .cells (Ruler.rb (P + 1)) (P + 1) }) := by
  have hh := (PacketsKeys.Pow.markR_lruns W P hP).dockK ![(RL : Fin (4 + NR + NO))] (fun i j _ => Subsingleton.elim i j)
    (roles s) (by intro j; fin_cases j; exact (roles_RL s).trans hr) [0] (by intro j hj; fin_cases j; simp at hj)
  have e : ([0] : List (Fin 1)).foldr (fun j ρ => Function.update ρ
      ((![(RL : Fin (4 + NR + NO))] : Fin 1 → Fin (4 + NR + NO)) j)
      ((![.cells (Ruler.rb (P + 1)) (P + 1)] : Fin 1 → TS) j))
      (roles s) = Function.update (roles s) RL (.cells (Ruler.rb (P + 1)) (P + 1)) := rfl
  rw [e, upd_RL] at hh
  exact hh

theorem finishR_run (hr : s.rl = .cells (Ruler.rb (W + 1)) (W + 1)) :
    LRuns W (mFinishR (NR := NR) (NO := NO)) (W + 3) (roles s) (roles { s with rl := .ruler }) := by
  have hh := (Ruler.finish_lruns W).dockK ![(RL : Fin (4 + NR + NO))] (fun i j _ => Subsingleton.elim i j)
    (roles s) (by intro j; fin_cases j; exact (roles_RL s).trans hr) [0] (by intro j hj; fin_cases j; simp at hj)
  have e : ([0] : List (Fin 1)).foldr (fun j ρ => Function.update ρ
      ((![(RL : Fin (4 + NR + NO))] : Fin 1 → Fin (4 + NR + NO)) j) ((![.ruler] : Fin 1 → TS) j))
      (roles s) = Function.update (roles s) RL .ruler := rfl
  rw [e, upd_RL] at hh
  exact hh

theorem appendR_run (k : ℕ) (hk : 1 ≤ k) (mk sm : Fin NO) (hne : mk.val ≠ sm.val) (n P : ℕ) (hP : 1 ≤ P)
    (f : ℕ → Bool) (hm : s.ot mk = .cells (sf (List.replicate n true)) 1) (hs : s.ot sm = .cells f 1)
    (hr : s.rl = .cells (Ruler.rb P) P) :
    LRuns W (mAppendR k mk sm) ((k + 1) * n + n + 7) (roles s)
      (roles { s with rl := .cells (Ruler.rb (P + k * n)) (P + k * n) }) := by
  have hinj : Function.Injective ![(os mk : Fin (4 + NR + NO)), os sm, RL] := by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [RL, os] at hv ⊢ <;> omega
  have hh := (Ruler.append_lruns W k hk n P hP f).dockK ![(os mk : Fin (4 + NR + NO)), os sm, RL] hinj (roles s)
    (by intro j; fin_cases j
        · exact (roles_os s mk).trans hm
        · exact (roles_os s sm).trans hs
        · exact (roles_RL s).trans hr) [2] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have e : ([2] : List (Fin 3)).foldr (fun j ρ => Function.update ρ
      ((![(os mk : Fin (4 + NR + NO)), os sm, RL] : Fin 3 → Fin (4 + NR + NO)) j)
      ((![.cells (sf (List.replicate n true)) 1, .cells f 1, .cells (Ruler.rb (P + k * n)) (P + k * n)] :
        Fin 3 → TS) j)) (roles s) = Function.update (roles s) RL (.cells (Ruler.rb (P + k * n)) (P + k * n)) := rfl
  rw [e, upd_RL] at hh
  exact hh

end Ruler

/-! ## Record equalities -/

section Eqs
variable {NR NO : ℕ}

theorem st_eq {x y : St NR NO} (h1 : x.rl = y.rl) (h2 : x.fl = y.fl) (h3 : x.rg = y.rg) (h4 : x.ot = y.ot) :
    x = y := by
  cases x; cases y; simp_all

end Eqs

/-! ## A register loaded from a unary word -/

section Load
variable {NR NO : ℕ}

/-- `x := v` from the unary `1^v` on `u` (partner `d`, a blank tape moving with it). -/
def loadU (x : Fin NR) (d u : Fin NO) :=
  Composition.machine (mZero (NO := NO) x) (Loop (mBit (NR := NR) d u) (mInc x) FL)

def ldSt (s : St NR NO) (x : Fin NR) (d u : Fin NO) (v c h : ℕ) (f : Bool) : St NR NO :=
  { s with rg := Function.update s.rg x c,
           ot := Function.update (Function.update s.ot d (.cells blank h)) u (.cells (PacketsKeys.Pow.u v) h),
           fl := f }

def loadCost (W v : ℕ) : ℕ := (2 * W + 3) + 1 + (v + 1) * (1 + (2 * W + 3) + 2)

variable {W : ℕ} (s : St NR NO)

theorem loadU_run (hr : s.rl = .ruler) (x : Fin NR) (d u : Fin NO) (hdu : d.val ≠ u.val) (v : ℕ)
    (hv : v < 2 ^ W) (hd : s.ot d = .cells blank 0) (hu : s.ot u = .cells (PacketsKeys.Pow.u v) 0) :
    LRuns W (loadU x d u) (loadCost W v) (roles s) (roles (ldSt s x d u v v (v + 1) false)) := by
  have hne : d ≠ u := fun e => hdu (congrArg Fin.val e)
  have h0 := zero_run (W := W) s hr x
  have e0 : ({ s with rg := Function.update s.rg x 0, fl := false } : St NR NO) = ldSt s x d u v 0 0 false := by
    refine st_eq rfl rfl rfl ?_
    show s.ot = Function.update (Function.update s.ot d (.cells blank 0)) u (.cells (PacketsKeys.Pow.u v) 0)
    rw [← hd, ← hu, Function.update_eq_self, Function.update_eq_self]
  rw [e0] at h0
  have hl := Loop.runs (W := W) (mBit (NR := NR) d u) (mInc (NO := NO) x) FL
    (fun i => roles (ldSt s x d u v i i false)) (fun i => roles (ldSt s x d u v i (i + 1) (decide (i < v)))) v
    (fun i _ => by
      have hb := bit_run (W := W) (ldSt s x d u v i i false) d u hdu (PacketsKeys.Pow.u v) blank i
        (by simp [ldSt]) (by simp [ldSt, Function.update_of_ne hne])
      refine hb.congr_out (congrArg roles (st_eq rfl rfl rfl ?_))
      funext k
      simp only [ldSt, Function.update_apply]
      split_ifs <;> simp_all [PacketsKeys.Pow.u])
    (fun i _ => rfl)
    (fun i hi => by
      have hb := inc_run (W := W) (ldSt s x d u v i (i + 1) (decide (i < v))) hr x
        (by simp [ldSt]; omega)
      refine hb.congr_out (congrArg roles (st_eq rfl rfl ?_ rfl))
      simp [ldSt])
  have hall := h0.seq hl
  refine hall.congr_out (congrArg roles (st_eq rfl ?_ rfl rfl))
  simp [ldSt]

end Load

/-! ## The ruler extended by a unary word -/

section Ext
variable {NR NO : ℕ}

/-- Mark `v` more ruler cells, `v` read from the unary `1^v` on `u` (partner `d`). -/
def extR (d u : Fin NO) :=
  Composition.machine (mPeek (NR := NR) d) (Loop (mBit (NR := NR) d u) (Composition.machine mMarkR (mPeek d)) FL)

def rrSt (s : St NR NO) (d u : Fin NO) (v R h : ℕ) (f : Bool) : St NR NO :=
  { s with rl := .cells (Ruler.rb R) R,
           ot := Function.update (Function.update s.ot d (.cells blank h)) u (.cells (PacketsKeys.Pow.u v) h),
           fl := f }

def extCost (v : ℕ) : ℕ := 1 + 1 + (v + 1) * (1 + (1 + 1 + 1) + 2)

variable {W : ℕ} (s : St NR NO)

theorem extR_run (d u : Fin NO) (hdu : d.val ≠ u.val) (v P : ℕ) (hP : 1 ≤ P) (hr : s.rl = .cells (Ruler.rb P) P)
    (hd : s.ot d = .cells blank 0) (hu : s.ot u = .cells (PacketsKeys.Pow.u v) 0) :
    LRuns W (extR (NR := NR) d u) (extCost v) (roles s) (roles (rrSt s d u v (P + v) (v + 1) false)) := by
  have hne : d ≠ u := fun e => hdu (congrArg Fin.val e)
  have h0 := peek_run (W := W) s d blank 0 hd
  have e0 : ({ s with fl := blank 0 } : St NR NO) = rrSt s d u v (P + 0) 0 false := by
    refine st_eq ?_ rfl rfl ?_
    · rw [Nat.add_zero]; exact hr
    · show s.ot = Function.update (Function.update s.ot d (.cells blank 0)) u (.cells (PacketsKeys.Pow.u v) 0)
      rw [← hd, ← hu, Function.update_eq_self, Function.update_eq_self]
  rw [e0] at h0
  have hl := Loop.runs (W := W) (mBit (NR := NR) d u) (Composition.machine mMarkR (mPeek d)) FL
    (fun i => roles (rrSt s d u v (P + i) i false)) (fun i => roles (rrSt s d u v (P + i) (i + 1) (decide (i < v)))) v
    (fun i _ => by
      have hb := bit_run (W := W) (rrSt s d u v (P + i) i false) d u hdu (PacketsKeys.Pow.u v) blank i
        (by simp [rrSt]) (by simp [rrSt, Function.update_of_ne hne])
      refine hb.congr_out (congrArg roles (st_eq rfl rfl rfl ?_))
      funext k
      simp only [rrSt, Function.update_apply]
      split_ifs <;> simp_all [PacketsKeys.Pow.u])
    (fun i _ => rfl)
    (fun i hi => by
      have h1 := markR_run (W := W) (rrSt s d u v (P + i) (i + 1) (decide (i < v))) (P + i) (by omega) rfl
      have h2 := peek_run (W := W) ({ rrSt s d u v (P + i) (i + 1) (decide (i < v)) with
        rl := .cells (Ruler.rb (P + i + 1)) (P + i + 1) }) d blank (i + 1)
        (by simp [rrSt, Function.update_of_ne hne])
      refine (h1.seq h2).congr_out (congrArg roles (st_eq ?_ rfl rfl rfl))
      simp [rrSt, Nat.add_assoc])
  have hall := h0.seq hl
  have hall' := (hall.congr_out (congrArg roles (show rrSt s d u v (P + v) (v + 1) (decide (v < v)) =
    rrSt s d u v (P + v) (v + 1) false by simp))).enlarge
    (show 1 + 1 + (v + 1) * (1 + (1 + 1 + 1) + 2) ≤ extCost v from le_rfl)
  exact hall'

end Ext

/-! ## `r := x mod p` -/

section ModP
variable {NR NO : ℕ}

/-- The round: `msk := 2·msk; r := 2r; t := 2t` (the bit shifted out of `t`), `r := r + bit`, `r := r mod p`. -/
def modBody (p r t msk : Fin NR) :=
  Composition.machine (mShl (NO := NO) msk) (Composition.machine (mShl (NO := NO) r)
    (Composition.machine (mShl (NO := NO) t)
      (Composition.machine (Ite (nop (4 + NR + NO)) (mInc (NO := NO) r) (nop (4 + NR + NO)) FL)
        (Composition.machine (mLt (NO := NO) r p) (Ite (nop (4 + NR + NO)) (mClr (NO := NO) r) (mSub (NO := NO) r p) FL)))))

/-- `r := x mod p` (registers `x`, `p` unchanged; the work registers `t`, `msk` end at `0`). -/
def modP (x p r t msk : Fin NR) :=
  Composition.machine (mZero (NO := NO) r) (Composition.machine (mCpy (NO := NO) t x)
    (Composition.machine (mZero (NO := NO) msk) (Composition.machine (mInc (NO := NO) msk)
      (Loop (mPos (NO := NO) msk) (modBody (NO := NO) p r t msk) FL))))

def modBodyCost (W : ℕ) : ℕ :=
  (2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((0 + (2 * W + 3) + 0 + 2) + 1 +
    ((2 * W + 3) + 1 + (0 + (2 * W + 3) + (2 * W + 3) + 2)))))

def modCost (W : ℕ) : ℕ :=
  (2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 +
    (W + 1) * ((2 * W + 3) + modBodyCost W + 2))))

/-- The state inside `modP`. -/
def m3 (s : St NR NO) (r t msk : Fin NR) (vr vt vm : ℕ) (f : Bool) : St NR NO :=
  { s with rg := Function.update (Function.update (Function.update s.rg r vr) t vt) msk vm, fl := f }

variable {W : ℕ} (s : St NR NO)

theorem m3_rg_r (r t msk : Fin NR) (hrt : r ≠ t) (hrm : r ≠ msk) (vr vt vm : ℕ) (f : Bool) :
    (m3 s r t msk vr vt vm f).rg r = vr := by
  simp [m3, Function.update_of_ne hrt, Function.update_of_ne hrm]

theorem m3_rg_t (r t msk : Fin NR) (htm : t ≠ msk) (vr vt vm : ℕ) (f : Bool) :
    (m3 s r t msk vr vt vm f).rg t = vt := by
  simp [m3, Function.update_of_ne htm]

theorem m3_rg_m (r t msk : Fin NR) (vr vt vm : ℕ) (f : Bool) : (m3 s r t msk vr vt vm f).rg msk = vm := by
  simp [m3]

theorem m3_rg_o (r t msk y : Fin NR) (hyr : y ≠ r) (hyt : y ≠ t) (hym : y ≠ msk) (vr vt vm : ℕ) (f : Bool) :
    (m3 s r t msk vr vt vm f).rg y = s.rg y := by
  simp [m3, Function.update_of_ne hyr, Function.update_of_ne hyt, Function.update_of_ne hym]

theorem m3_set_r (r t msk : Fin NR) (hrt : r ≠ t) (hrm : r ≠ msk) (vr vt vm v : ℕ) (f f' : Bool) :
    ({ m3 s r t msk vr vt vm f with rg := Function.update (m3 s r t msk vr vt vm f).rg r v, fl := f' } : St NR NO) =
      m3 s r t msk v vt vm f' := by
  refine st_eq rfl rfl ?_ rfl
  funext y
  simp only [m3, Function.update_apply]
  split_ifs <;> simp_all

theorem m3_set_t (r t msk : Fin NR) (htm : t ≠ msk) (vr vt vm v : ℕ) (f f' : Bool) :
    ({ m3 s r t msk vr vt vm f with rg := Function.update (m3 s r t msk vr vt vm f).rg t v, fl := f' } : St NR NO) =
      m3 s r t msk vr v vm f' := by
  refine st_eq rfl rfl ?_ rfl
  funext y
  simp only [m3, Function.update_apply]
  split_ifs <;> simp_all

theorem m3_set_m (r t msk : Fin NR) (vr vt vm v : ℕ) (f f' : Bool) :
    ({ m3 s r t msk vr vt vm f with rg := Function.update (m3 s r t msk vr vt vm f).rg msk v, fl := f' } : St NR NO) =
      m3 s r t msk vr vt v f' := by
  refine st_eq rfl rfl ?_ rfl
  funext y
  simp only [m3, Function.update_apply]
  split_ifs <;> simp_all

theorem modBody_run (hr : s.rl = .ruler) (x p r t msk : Fin NR)
    (hpr : p ≠ r) (hpt : p ≠ t) (hpm : p ≠ msk) (hrt : r ≠ t) (hrm : r ≠ msk) (htm : t ≠ msk)
    (hX : s.rg x < 2 ^ W) (hP : 0 < s.rg p) (hP2 : 2 * s.rg p ≤ 2 ^ W) (i : ℕ) (hi : i < W) :
    LRuns W (modBody (NO := NO) p r t msk) (modBodyCost W)
      (roles (m3 s r t msk (s.rg x / 2 ^ (W - i) % s.rg p) (Mul.tv W (s.rg x) i) (Mul.mv W i) (decide (i < W))))
      (roles (m3 s r t msk (s.rg x / 2 ^ (W - (i + 1)) % s.rg p) (Mul.tv W (s.rg x) (i + 1)) (Mul.mv W (i + 1))
        false)) := by
  set X := s.rg x with hXd
  set P := s.rg p with hPd
  set R := X / 2 ^ (W - i) % P with hR
  have hRP : R < P := Nat.mod_lt _ hP
  obtain ⟨rf1, rf2, rf3⟩ := Mul.round_facts W X i hi
  set b := Mul.bv W X i with hb
  have hrm0 : 2 * R % 2 ^ W = 2 * R := Nat.mod_eq_of_lt (by omega)
  have hr0 : decide (2 ^ W ≤ 2 * R) = false := by simp; omega
  -- step 1: the mask
  have s1 := shl_run (W := W) (m3 s r t msk R (Mul.tv W X i) (Mul.mv W i) (decide (i < W))) hr msk
    (by rw [m3_rg_m]; exact Mul.mv_lt W i)
  rw [m3_set_m s r t msk, m3_rg_m, Mul.mv_succ W i hi] at s1
  -- step 2: `r := 2r`
  have s2 := shl_run (W := W) (m3 s r t msk R (Mul.tv W X i) (Mul.mv W (i + 1))
    (decide (2 ^ W ≤ 2 * Mul.mv W i))) hr r (by rw [m3_rg_r s r t msk hrt hrm]; omega)
  rw [m3_set_r s r t msk hrt hrm, m3_rg_r s r t msk hrt hrm, hrm0, hr0] at s2
  -- step 3: `t := 2t`, the bit
  have s3 := shl_run (W := W) (m3 s r t msk (2 * R) (Mul.tv W X i) (Mul.mv W (i + 1)) false) hr t
    (by rw [m3_rg_t s r t msk htm]; exact Mul.tv_lt W X i hi.le)
  rw [m3_set_t s r t msk htm, m3_rg_t s r t msk htm, rf1, rf2] at s3
  -- step 4: `r := r + bit`
  have s4 := Ite.runs (W := W) (nop (4 + NR + NO)) (mInc (NO := NO) r) (nop (4 + NR + NO)) FL b
    (nop_lruns _) (roles_FL _)
    (ρ := roles (m3 s r t msk (2 * R + b.toNat) (Mul.tv W X (i + 1)) (Mul.mv W (i + 1)) false))
    (fun hbt => by
      have h := inc_run (W := W) (m3 s r t msk (2 * R) (Mul.tv W X (i + 1)) (Mul.mv W (i + 1)) b) hr r
        (by rw [m3_rg_r s r t msk hrt hrm]; omega)
      rw [m3_set_r s r t msk hrt hrm, m3_rg_r s r t msk hrt hrm] at h
      rw [hbt]
      exact h)
    (fun hbf => by
      rw [hbf, Bool.toNat_false, Nat.add_zero]
      rw [hbf] at s3
      exact nop_lruns _)
  -- step 5: `flag := r < p`
  have hb1 : b.toNat ≤ 1 := by cases b <;> simp
  have s5 := lt_run (W := W) (m3 s r t msk (2 * R + b.toNat) (Mul.tv W X (i + 1)) (Mul.mv W (i + 1)) false) hr r p
    hpr.symm (by rw [m3_rg_r s r t msk hrt hrm]; omega) (by rw [m3_rg_o s r t msk p hpr hpt hpm]; omega)
  rw [m3_rg_r s r t msk hrt hrm, m3_rg_o s r t msk p hpr hpt hpm] at s5
  -- step 6: `r := r mod p`
  have s6 := Ite.runs (W := W) (nop (4 + NR + NO)) (mClr (NO := NO) r) (mSub (NO := NO) r p) FL
    (decide (2 * R + b.toNat < P)) (nop_lruns _) (roles_FL _)
    (ρ := roles (m3 s r t msk ((2 * R + b.toNat) % P) (Mul.tv W X (i + 1)) (Mul.mv W (i + 1)) false))
    (fun hc => by
      have hc' : 2 * R + b.toNat < P := by simpa using hc
      have h := clr_run (W := W) (m3 s r t msk (2 * R + b.toNat) (Mul.tv W X (i + 1)) (Mul.mv W (i + 1))
        (decide (2 * R + b.toNat < P))) hr r (by rw [m3_rg_r s r t msk hrt hrm]; omega)
      rw [Nat.mod_eq_of_lt hc']
      exact h)
    (fun hc => by
      have hc' : P ≤ 2 * R + b.toNat := by simpa using hc
      have h := sub_run (W := W) (m3 s r t msk (2 * R + b.toNat) (Mul.tv W X (i + 1)) (Mul.mv W (i + 1))
        (decide (2 * R + b.toNat < P))) hr r p hpr.symm (by rw [m3_rg_r s r t msk hrt hrm]; omega)
        (by rw [m3_rg_o s r t msk p hpr hpt hpm]; omega)
        (by rw [m3_rg_o s r t msk p hpr hpt hpm, m3_rg_r s r t msk hrt hrm]; exact hc')
      rw [m3_set_r s r t msk hrt hrm, m3_rg_r s r t msk hrt hrm, m3_rg_o s r t msk p hpr hpt hpm] at h
      have e : (2 * R + b.toNat) % P = 2 * R + b.toNat - P := by
        rw [Nat.mod_eq_sub_mod hc', Nat.mod_eq_of_lt (by omega)]
      rw [e]
      exact h)
  have hall := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))
  have hfin : (2 * R + b.toNat) % P = X / 2 ^ (W - (i + 1)) % P := by
    rw [rf3, hR]
    cases b <;> simp [Nat.add_mod, Nat.mul_mod]
  rw [hfin] at hall
  exact hall

theorem modP_run (hr : s.rl = .ruler) (x p r t msk : Fin NR) (hxr : x ≠ r) (hxt : x ≠ t)
    (hpr : p ≠ r) (hpt : p ≠ t) (hpm : p ≠ msk) (hrt : r ≠ t) (hrm : r ≠ msk) (htm : t ≠ msk)
    (hX : s.rg x < 2 ^ W) (hP : 0 < s.rg p) (hP2 : 2 * s.rg p ≤ 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (modP (NO := NO) x p r t msk) (modCost W) (roles s)
      (roles (m3 s r t msk (s.rg x % s.rg p) 0 0 false)) := by
  set X := s.rg x with hXd
  set P := s.rg p with hPd
  have hPW : P < 2 ^ W := by omega
  -- the prologue
  have e1 := zero_run (W := W) s hr r
  have e2 := cpy_run (W := W) { s with rg := Function.update s.rg r 0, fl := false } hr t x (Ne.symm hxt)
    (by show Function.update s.rg r 0 x < 2 ^ W; rw [Function.update_of_ne hxr]; exact hX)
  have e3 := zero_run (W := W) { { s with rg := Function.update s.rg r 0, fl := false } with
    rg := Function.update (Function.update s.rg r 0) t ((Function.update s.rg r 0) x), fl := false } hr msk
  have e4 := inc_run (W := W) { { { s with rg := Function.update s.rg r 0, fl := false } with
    rg := Function.update (Function.update s.rg r 0) t ((Function.update s.rg r 0) x), fl := false } with
    rg := Function.update (Function.update (Function.update s.rg r 0) t ((Function.update s.rg r 0) x)) msk 0,
    fl := false } hr msk (by simp only [Function.update_self]; exact Nat.one_lt_two_pow_iff.mpr (by omega))
  have hst0 : roles ({ { { { s with rg := Function.update s.rg r 0, fl := false } with
      rg := Function.update (Function.update s.rg r 0) t ((Function.update s.rg r 0) x), fl := false } with
      rg := Function.update (Function.update (Function.update s.rg r 0) t ((Function.update s.rg r 0) x)) msk 0,
      fl := false } with
      rg := Function.update (Function.update (Function.update (Function.update s.rg r 0) t
        ((Function.update s.rg r 0) x)) msk 0) msk
        ((Function.update (Function.update (Function.update s.rg r 0) t ((Function.update s.rg r 0) x)) msk 0) msk + 1),
      fl := false } : St NR NO) =
      roles (m3 s r t msk (X / 2 ^ (W - 0) % P) (Mul.tv W X 0) (Mul.mv W 0) false) := by
    congr 1
    refine st_eq rfl rfl ?_ rfl
    rw [Nat.sub_zero, Nat.div_eq_of_lt hX, Nat.zero_mod, Mul.tv_zero W X hX, Mul.mv_zero W hW]
    funext y
    simp only [m3, Function.update_apply]
    split_ifs <;> simp_all
  rw [hst0] at e4
  -- the rounds
  have hl := Loop.runs (W := W) (nb := modBodyCost W) (mPos (NO := NO) msk) (modBody (NO := NO) p r t msk) FL
    (fun i => roles (m3 s r t msk (X / 2 ^ (W - i) % P) (Mul.tv W X i) (Mul.mv W i) false))
    (fun i => roles (m3 s r t msk (X / 2 ^ (W - i) % P) (Mul.tv W X i) (Mul.mv W i) (decide (i < W)))) W
    (fun i hi => by
      have h := pos_run (W := W) (m3 s r t msk (X / 2 ^ (W - i) % P) (Mul.tv W X i) (Mul.mv W i) false) hr msk
        (by rw [m3_rg_m]; exact Mul.mv_lt W i)
      refine h.congr_out (congrArg roles (st_eq rfl ?_ rfl rfl))
      show decide (0 < (m3 s r t msk _ _ (Mul.mv W i) false).rg msk) = decide (i < W)
      rw [m3_rg_m]
      exact Mul.mv_pos W i hi)
    (fun i _ => rfl)
    (fun i hi => modBody_run s hr x p r t msk hpr hpt hpm hrt hrm htm hX hP hP2 i hi)
  have hall := (e1.seq (e2.seq (e3.seq (e4.seq hl)))).congr_out (congrArg roles (show m3 s r t msk (X / 2 ^ (W - W) % P) (Mul.tv W X W)
      (Mul.mv W W) (decide (W < W)) = m3 s r t msk (X % P) 0 0 false by
    rw [Nat.sub_self, pow_zero, Nat.div_one, Mul.tv_W, Mul.mv_W]
    simp))
  refine hall.enlarge ?_
  unfold modCost
  omega

end ModP

/-! ## `flag := testBit j r` -/

theorem testBit_mod (R j : ℕ) : R.testBit j = decide (2 ^ j ≤ R % 2 ^ (j + 1)) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.mod_pow_succ]
  have h1 : R % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
  have h2 : R / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases h : R / 2 ^ j % 2 = 1
  · rw [h]; simp
  · have h0 : R / 2 ^ j % 2 = 0 := by omega
    rw [h0]; simp; omega

section TestB
variable {NR NO : ℕ}

/-- `flag := testBit j r`, from `e2 = 2^(j+1)`, `e2m = 2^(j+1) - 1`, `em = 2^j - 1` (work register `t`). -/
def testB (r e2 e2m em t : Fin NR) :=
  Composition.machine (mCpy (NO := NO) t r)
    (Composition.machine (Loop (mLt (NO := NO) e2m t) (mSub (NO := NO) t e2) FL) (mLt (NO := NO) em t))

def testCost (W Bd : ℕ) : ℕ := (2 * W + 3) + 1 + ((Bd + 1) * ((2 * W + 3) + (2 * W + 3) + 2) + 1 + (2 * W + 3))

def tb (s : St NR NO) (t : Fin NR) (vt : ℕ) (f : Bool) : St NR NO :=
  { s with rg := Function.update s.rg t vt, fl := f }

variable {W : ℕ} (s : St NR NO)

theorem testB_run (hr : s.rl = .ruler) (r e2 e2m em t : Fin NR) (htr : t ≠ r) (hte : t ≠ e2) (htm : t ≠ e2m)
    (htn : t ≠ em) (j Bd : ℕ) (hE2 : s.rg e2 = 2 ^ (j + 1)) (hE2m : s.rg e2m = 2 ^ (j + 1) - 1)
    (hEm : s.rg em = 2 ^ j - 1) (hR : s.rg r < 2 ^ W) (hRB : s.rg r ≤ Bd) (hEW : 2 ^ (j + 1) < 2 ^ W) :
    LRuns W (testB (NO := NO) r e2 e2m em t) (testCost W Bd) (roles s)
      (roles (tb s t (s.rg r % 2 ^ (j + 1)) ((s.rg r).testBit j))) := by
  set R := s.rg r with hRd
  have hE0 : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
  have e1 := cpy_run (W := W) s hr t r htr hR
  have hl := Loop.runs (W := W) (mLt (NO := NO) e2m t) (mSub (NO := NO) t e2) FL
    (fun i => roles (tb s t (R - i * 2 ^ (j + 1)) false))
    (fun i => roles (tb s t (R - i * 2 ^ (j + 1)) (decide (i < R / 2 ^ (j + 1))))) (R / 2 ^ (j + 1))
    (fun i hi => by
      have h := lt_run (W := W) (tb s t (R - i * 2 ^ (j + 1)) false) hr e2m t (Ne.symm htm)
        (by simp [tb, Function.update_of_ne (Ne.symm htm)]; rw [hE2m]; omega)
        (by simp [tb]; omega)
      refine h.congr_out (congrArg roles (st_eq rfl ?_ rfl rfl))
      simp only [tb, Function.update_self, Function.update_of_ne (Ne.symm htm), hE2m]
      have h1 : i * 2 ^ (j + 1) ≤ R := by
        have := (Nat.le_div_iff_mul_le hE0).mp hi
        exact this
      apply dec_congr
      constructor
      · intro h2
        have : (i + 1) * 2 ^ (j + 1) ≤ R := by rw [Nat.add_mul]; omega
        have := (Nat.le_div_iff_mul_le hE0).mpr this
        omega
      · intro h2
        have : (i + 1) * 2 ^ (j + 1) ≤ R := (Nat.le_div_iff_mul_le hE0).mp h2
        rw [Nat.add_mul] at this
        omega)
    (fun i _ => rfl)
    (fun i hi => by
      have hle : (i + 1) * 2 ^ (j + 1) ≤ R := (Nat.le_div_iff_mul_le hE0).mp hi
      have h := sub_run (W := W) (tb s t (R - i * 2 ^ (j + 1)) (decide (i < R / 2 ^ (j + 1)))) hr t e2 hte
        (by simp [tb]; omega) (by simp [tb, Function.update_of_ne (Ne.symm hte)]; omega)
        (by simp [tb, Function.update_of_ne (Ne.symm hte)]; rw [Nat.add_mul] at hle; omega)
      refine h.congr_out (congrArg roles (st_eq rfl rfl ?_ rfl))
      simp only [tb, Function.update_self, Function.update_of_ne (Ne.symm hte), hE2, Function.update_idem]
      congr 1
      rw [Nat.add_mul]
      omega)
  have e3 := lt_run (W := W) (tb s t (R - R / 2 ^ (j + 1) * 2 ^ (j + 1)) (decide (R / 2 ^ (j + 1) < R / 2 ^ (j + 1))))
    hr em t (Ne.symm htn) (by simp [tb, Function.update_of_ne (Ne.symm htn)]; rw [hEm]; omega) (by simp [tb]; omega)
  have hmod : R - R / 2 ^ (j + 1) * 2 ^ (j + 1) = R % 2 ^ (j + 1) := by
    rw [Nat.mod_eq_sub_div_mul]
  have e1' := e1.congr_out (congrArg roles (show ({ s with rg := Function.update s.rg t (s.rg r), fl := false } :
    St NR NO) = tb s t (R - 0 * 2 ^ (j + 1)) false by simp [tb, hRd]))
  have hall := e1'.seq ((hl.seq e3))
  refine (hall.congr_out (congrArg roles (a₂ := tb s t (R % 2 ^ (j + 1)) (R.testBit j))
    (st_eq rfl ?_ ?_ rfl))).enlarge ?_
  · simp only [tb, Function.update_self, Function.update_of_ne (Ne.symm htn), hEm, hmod]
    rw [testBit_mod]
    apply dec_congr
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  · simp only [tb, hmod]
  · unfold testCost
    have hn : R / 2 ^ (j + 1) ≤ Bd := le_trans (Nat.div_le_self _ _) hRB
    have := Nat.mul_le_mul_right ((2 * W + 3) + (2 * W + 3) + 2) (show R / 2 ^ (j + 1) + 1 ≤ Bd + 1 by omega)
    omega

end TestB

/-! ## Powers of two -/

section Pow2
variable {NR NO : ℕ}

/-- From `jc = J`: `e := 2^J`, `ep := 2^(J-1)` (`0` if `J = 0`), `jc := 0`. -/
def pow2 (jc e ep : Fin NR) :=
  Composition.machine (mZero (NO := NO) ep) (Composition.machine (mZero (NO := NO) e)
    (Composition.machine (mInc (NO := NO) e)
      (Loop (mPos (NO := NO) jc)
        (Composition.machine (mCpy (NO := NO) ep e) (Composition.machine (mShl (NO := NO) e) (mDec (NO := NO) jc))) FL)))

def pow2Cost (W J : ℕ) : ℕ :=
  (2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 +
    (J + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3))) + 2)))

def p2 (s : St NR NO) (jc e ep : Fin NR) (vj ve vp : ℕ) (f : Bool) : St NR NO :=
  { s with rg := Function.update (Function.update (Function.update s.rg jc vj) e ve) ep vp, fl := f }

variable {W : ℕ} (s : St NR NO)

theorem pow2_run (hr : s.rl = .ruler) (jc e ep : Fin NR) (hje : jc ≠ e) (hjp : jc ≠ ep) (hep : e ≠ ep)
    (hJW : s.rg jc < W) :
    LRuns W (pow2 (NO := NO) jc e ep) (pow2Cost W (s.rg jc)) (roles s)
      (roles (p2 s jc e ep 0 (2 ^ s.rg jc) (2 ^ s.rg jc / 2) false)) := by
  set J := s.rg jc with hJd
  have hJ2 : J < 2 ^ W := lt_trans hJW Nat.lt_two_pow_self
  have hpw : ∀ i, i ≤ J → 2 ^ i < 2 ^ W := fun i hi => Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e1 := zero_run (W := W) s hr ep
  have e2 := zero_run (W := W) { s with rg := Function.update s.rg ep 0, fl := false } hr e
  have e3 := inc_run (W := W) { { s with rg := Function.update s.rg ep 0, fl := false } with
    rg := Function.update (Function.update s.rg ep 0) e 0, fl := false } hr e
    (by simp only [Function.update_self]; exact Nat.one_lt_two_pow_iff.mpr (by omega))
  have hs0 : ({ { { s with rg := Function.update s.rg ep 0, fl := false } with
      rg := Function.update (Function.update s.rg ep 0) e 0, fl := false } with
      rg := Function.update (Function.update (Function.update s.rg ep 0) e 0) e
        ((Function.update (Function.update s.rg ep 0) e 0) e + 1), fl := false } : St NR NO) =
      p2 s jc e ep (J - 0) (2 ^ 0) (2 ^ 0 / 2) false := by
    refine st_eq rfl rfl ?_ rfl
    funext y
    simp only [p2, Function.update_apply]
    split_ifs <;> simp_all
  rw [hs0] at e3
  have hl := Loop.runs (W := W) (mPos (NO := NO) jc)
    (Composition.machine (mCpy (NO := NO) ep e) (Composition.machine (mShl (NO := NO) e) (mDec (NO := NO) jc))) FL
    (fun i => roles (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) false))
    (fun i => roles (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J)))) J
    (fun i hi => by
      have h := pos_run (W := W) (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) false) hr jc
        (by simp [p2, Function.update_of_ne hje, Function.update_of_ne hjp]; omega)
      refine h.congr_out (congrArg roles (st_eq rfl ?_ rfl rfl))
      simp only [p2, Function.update_self, Function.update_of_ne hje, Function.update_of_ne hjp]
      apply dec_congr
      omega)
    (fun i _ => rfl)
    (fun i hi => by
      have h1 := cpy_run (W := W) (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))) hr ep e hep.symm
        (by simp [p2, Function.update_of_ne hep]; exact hpw i hi.le)
      have h2 := shl_run (W := W) { p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J)) with
        rg := Function.update (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg ep
          ((p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg e), fl := false } hr e
        (by simp [p2, Function.update_of_ne hep]; exact hpw i hi.le)
      have h3 := dec_run (W := W) { { p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J)) with
        rg := Function.update (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg ep
          ((p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg e), fl := false } with
        rg := Function.update (Function.update (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg ep
          ((p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg e)) e
          (2 * (Function.update (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg ep
            ((p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg e)) e % 2 ^ W),
        fl := decide (2 ^ W ≤ 2 * (Function.update (p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg ep
            ((p2 s jc e ep (J - i) (2 ^ i) (2 ^ i / 2) (decide (i < J))).rg e)) e) } hr jc
        (by simp [p2, Function.update_of_ne hje, Function.update_of_ne hjp]; omega)
        (by simp [p2, Function.update_of_ne hje, Function.update_of_ne hjp]; omega)
      refine (h1.seq (h2.seq h3)).congr_out (congrArg roles (st_eq rfl rfl ?_ rfl))
      have hlt : 2 * 2 ^ i < 2 ^ W := by rw [← pow_succ']; exact hpw (i + 1) hi
      have hsh : 2 * 2 ^ i % 2 ^ W = 2 ^ (i + 1) := by rw [Nat.mod_eq_of_lt hlt, pow_succ]; ring
      have hsh2 : 2 ^ (i + 1) / 2 = 2 ^ i := by rw [pow_succ]; simp
      funext y
      simp only [p2, Function.update_apply]
      split_ifs <;> simp_all <;> omega)
  have hall := e1.seq (e2.seq (e3.seq hl))
  refine (hall.congr_out (congrArg roles (show p2 s jc e ep (J - J) (2 ^ J) (2 ^ J / 2) (decide (J < J)) =
    p2 s jc e ep 0 (2 ^ J) (2 ^ J / 2) false by simp))).enlarge ?_
  unfold pow2Cost
  omega

end Pow2

end
end NearCubicWires.PacketsKeys.RM

