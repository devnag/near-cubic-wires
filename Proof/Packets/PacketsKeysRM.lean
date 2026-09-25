import Proof.Packets.PacketsKeysPow
import Proof.Packets.PacketsSymExact

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

/-- A register-machine state. -/
structure St (NR NO : ℕ) where
  rl : TS
  fl : Bool
  rg : Fin NR → ℕ
  ot : Fin NO → TS

section Layout
variable {NR NO : ℕ}

/-- The role map of a state. -/
def roles (s : St NR NO) : Fin (4 + NR + NO) → TS := fun i =>
  if h0 : i.val < 4 then
    (if i.val = 0 then s.rl else if i.val = 1 then .flag s.fl else if i.val = 2 then .reg 0 else .cells blank 0)
  else if h : i.val < 4 + NR then .reg (s.rg ⟨i.val - 4, by omega⟩)
  else s.ot ⟨i.val - 4 - NR, by have := i.isLt; omega⟩

def RL : Fin (4 + NR + NO) := ⟨0, by omega⟩
def FL : Fin (4 + NR + NO) := ⟨1, by omega⟩
def ZR : Fin (4 + NR + NO) := ⟨2, by omega⟩
def UB : Fin (4 + NR + NO) := ⟨3, by omega⟩
def rs (x : Fin NR) : Fin (4 + NR + NO) := ⟨4 + x.val, by have := x.isLt; omega⟩
def os (k : Fin NO) : Fin (4 + NR + NO) := ⟨4 + NR + k.val, by have := k.isLt; omega⟩

theorem roles_RL (s : St NR NO) : roles s RL = s.rl := rfl
theorem roles_FL (s : St NR NO) : roles s FL = .flag s.fl := rfl
theorem roles_ZR (s : St NR NO) : roles s ZR = .reg 0 := rfl
theorem roles_UB (s : St NR NO) : roles s UB = .cells blank 0 := rfl

theorem roles_rs (s : St NR NO) (x : Fin NR) : roles s (rs x) = .reg (s.rg x) := by
  unfold roles rs
  simp only
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  apply Fin.ext
  simp

theorem roles_os (s : St NR NO) (k : Fin NO) : roles s (os k) = s.ot k := by
  unfold roles os
  simp only
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 1
  apply Fin.ext
  simp only
  omega

theorem upd_rs (s : St NR NO) (x : Fin NR) (v : ℕ) :
    Function.update (roles s) (rs x) (.reg v) = roles { s with rg := Function.update s.rg x v } := by
  funext i
  by_cases h : i = rs x
  · subst h
    rw [Function.update_self, roles_rs]
    simp
  · rw [Function.update_of_ne h]
    unfold roles
    split_ifs with h0 h1 h2 h3 h4 <;> try rfl
    congr 1
    symm
    apply Function.update_of_ne
    intro e
    apply h
    apply Fin.ext
    have := congrArg Fin.val e
    simp only [rs] at this ⊢
    omega

theorem upd_FL (s : St NR NO) (b : Bool) :
    Function.update (roles s) (FL : Fin (4 + NR + NO)) (.flag b) = roles { s with fl := b } := by
  funext i
  by_cases h : i = FL
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    have hv : i.val ≠ 1 := fun e => h (Fin.ext e)
    unfold roles
    split_ifs <;> first | rfl | (exfalso; omega)

theorem upd_RL (s : St NR NO) (t : TS) :
    Function.update (roles s) (RL : Fin (4 + NR + NO)) t = roles { s with rl := t } := by
  funext i
  by_cases h : i = RL
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    have hv : i.val ≠ 0 := fun e => h (Fin.ext e)
    unfold roles
    split_ifs <;> first | rfl | (exfalso; omega)

theorem upd_ZR (s : St NR NO) : Function.update (roles s) (ZR : Fin (4 + NR + NO)) (.reg 0) = roles s := by
  funext i
  by_cases h : i = ZR
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]

theorem upd_os (s : St NR NO) (k : Fin NO) (t : TS) :
    Function.update (roles s) (os k) t = roles { s with ot := Function.update s.ot k t } := by
  funext i
  by_cases h : i = os k
  · subst h
    rw [Function.update_self, roles_os]
    simp
  · rw [Function.update_of_ne h]
    unfold roles
    split_ifs with h0 h1 h2 h3 h4 <;> try rfl
    dsimp only
    symm
    apply Function.update_of_ne
    intro e
    apply h
    apply Fin.ext
    have := congrArg Fin.val e
    simp only [os] at this ⊢
    omega

/-! ### Distinct slots -/

theorem rs_ne {x y : Fin NR} (h : x ≠ y) : (rs x : Fin (4 + NR + NO)) ≠ rs y := by
  intro e
  apply h
  apply Fin.ext
  have := congrArg Fin.val e
  simp only [rs] at this
  omega

theorem d4 {x y : Fin NR} (h : x ≠ y) : D4 (RL : Fin (4 + NR + NO)) (rs x) (rs y) FL := by
  refine ⟨?_, ?_, ?_, rs_ne h, ?_, ?_⟩ <;> intro e <;> have := congrArg Fin.val e <;>
    simp only [RL, FL, rs] at this <;> omega

theorem d4z (x : Fin NR) : D4 (RL : Fin (4 + NR + NO)) (rs x) ZR FL := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> have := congrArg Fin.val e <;>
    simp only [RL, FL, rs, ZR] at this <;> omega

theorem d4zl (x : Fin NR) : D4 (RL : Fin (4 + NR + NO)) ZR (rs x) FL := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> have := congrArg Fin.val e <;>
    simp only [RL, FL, rs, ZR] at this <;> omega

end Layout

/-! ## Register instructions -/

section Instr
variable {NR NO : ℕ}

def mAdd (x y : Fin NR) := swAt addF false true (RL : Fin (4 + NR + NO)) (rs x) (rs y) FL
def mInc (x : Fin NR) := swAt addF true true (RL : Fin (4 + NR + NO)) (rs x) ZR FL
def mSub (x y : Fin NR) := swAt subF false true (RL : Fin (4 + NR + NO)) (rs x) (rs y) FL
def mDec (x : Fin NR) := swAt subF true true (RL : Fin (4 + NR + NO)) (rs x) ZR FL
/-- `flag := x < y`. -/
def mLt (x y : Fin NR) := swAt subF false false (RL : Fin (4 + NR + NO)) (rs x) (rs y) FL
/-- `flag := 0 < x`. -/
def mPos (x : Fin NR) := swAt subF false false (RL : Fin (4 + NR + NO)) ZR (rs x) FL
def mCpy (x y : Fin NR) := swAt copyF false true (RL : Fin (4 + NR + NO)) (rs x) (rs y) FL
def mZero (x : Fin NR) := swAt zeroF false true (RL : Fin (4 + NR + NO)) (rs x) ZR FL
def mShl (x : Fin NR) := swAt shlF false true (RL : Fin (4 + NR + NO)) (rs x) ZR FL
/-- `x := x + 0`: registers unchanged, `flag := false`. -/
def mClr (x : Fin NR) := swAt addF false true (RL : Fin (4 + NR + NO)) (rs x) ZR FL
/-- `z := x · y` (the scratch `t`, `m` end at `0`). -/
def mMul (x y z t m : Fin NR) :=
  RecoveryFocus.machine ![(RL : Fin (4 + NR + NO)), rs x, rs y, rs z, rs t, rs m, FL, ZR] Mul.machine

/-- The registers after a multiplication. -/
def mulRg (g : Fin NR → ℕ) (z t m : Fin NR) (v : ℕ) : Fin NR → ℕ :=
  Function.update (Function.update (Function.update g z v) t 0) m 0

variable {W : ℕ} (s : St NR NO) (hr : s.rl = .ruler)
include hr

theorem add_run (x y : Fin NR) (hxy : x ≠ y) (ha : s.rg x < 2 ^ W) (hb : s.rg y < 2 ^ W)
    (hab : s.rg x + s.rg y < 2 ^ W) :
    LRuns W (mAdd (NO := NO) x y) (2 * W + 3) (roles s)
      (roles { s with rg := Function.update s.rg x (s.rg x + s.rg y), fl := false }) := by
  have h := add_at (W := W) (roles s) RL (rs x) (rs y) FL (d4 hxy) (s.rg x) (s.rg y) s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_rs s y) (roles_FL s) ha hb hab
  rw [upd_rs, upd_FL] at h
  exact h

theorem inc_run (x : Fin NR) (ha : s.rg x + 1 < 2 ^ W) :
    LRuns W (mInc (NO := NO) x) (2 * W + 3) (roles s)
      (roles { s with rg := Function.update s.rg x (s.rg x + 1), fl := false }) := by
  have h := inc_at (W := W) (roles s) RL (rs x) ZR FL (d4z x) (s.rg x) 0 s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_ZR s) (roles_FL s) rfl ha
  rw [upd_rs, upd_FL] at h
  exact h

theorem sub_run (x y : Fin NR) (hxy : x ≠ y) (ha : s.rg x < 2 ^ W) (hb : s.rg y < 2 ^ W) (hba : s.rg y ≤ s.rg x) :
    LRuns W (mSub (NO := NO) x y) (2 * W + 3) (roles s)
      (roles { s with rg := Function.update s.rg x (s.rg x - s.rg y), fl := false }) := by
  have h := sub_at (W := W) (roles s) RL (rs x) (rs y) FL (d4 hxy) (s.rg x) (s.rg y) s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_rs s y) (roles_FL s) ha hb hba
  rw [upd_rs, upd_FL] at h
  exact h

theorem dec_run (x : Fin NR) (ha : s.rg x < 2 ^ W) (h1 : 1 ≤ s.rg x) :
    LRuns W (mDec (NO := NO) x) (2 * W + 3) (roles s)
      (roles { s with rg := Function.update s.rg x (s.rg x - 1), fl := false }) := by
  have h := dec_at (W := W) (roles s) RL (rs x) ZR FL (d4z x) (s.rg x) 0 s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_ZR s) (roles_FL s) rfl ha h1
  rw [upd_rs, upd_FL] at h
  exact h

theorem lt_run (x y : Fin NR) (hxy : x ≠ y) (ha : s.rg x < 2 ^ W) (hb : s.rg y < 2 ^ W) :
    LRuns W (mLt (NO := NO) x y) (2 * W + 3) (roles s) (roles { s with fl := decide (s.rg x < s.rg y) }) := by
  have h := lt_at (W := W) (roles s) RL (rs x) (rs y) FL (d4 hxy) (s.rg x) (s.rg y) s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_rs s y) (roles_FL s) ha hb
  rw [upd_rs, upd_FL] at h
  have e : Function.update s.rg x (s.rg x) = s.rg := Function.update_eq_self x s.rg
  rw [e] at h
  exact h

theorem pos_run (x : Fin NR) (ha : s.rg x < 2 ^ W) :
    LRuns W (mPos (NO := NO) x) (2 * W + 3) (roles s) (roles { s with fl := decide (0 < s.rg x) }) := by
  have h := lt_at (W := W) (roles s) RL ZR (rs x) FL (d4zl x) 0 (s.rg x) s.fl
    (by rw [roles_RL, hr]) (roles_ZR s) (roles_rs s x) (roles_FL s) (Nat.two_pow_pos W) ha
  rw [upd_ZR, upd_FL] at h
  exact h

theorem cpy_run (x y : Fin NR) (hxy : x ≠ y) (hb : s.rg y < 2 ^ W) :
    LRuns W (mCpy (NO := NO) x y) (2 * W + 3) (roles s)
      (roles { s with rg := Function.update s.rg x (s.rg y), fl := false }) := by
  have h := cpy_at (W := W) (roles s) RL (rs x) (rs y) FL (d4 hxy) (s.rg x) (s.rg y) s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_rs s y) (roles_FL s) hb
  rw [upd_rs, upd_FL] at h
  exact h

theorem zero_run (x : Fin NR) :
    LRuns W (mZero (NO := NO) x) (2 * W + 3) (roles s)
      (roles { s with rg := Function.update s.rg x 0, fl := false }) := by
  have h := zero_at (W := W) (roles s) RL (rs x) ZR FL (d4z x) (s.rg x) 0 s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_ZR s) (roles_FL s)
  rw [upd_rs, upd_FL] at h
  exact h

theorem shl_run (x : Fin NR) (ha : s.rg x < 2 ^ W) :
    LRuns W (mShl (NO := NO) x) (2 * W + 3) (roles s)
      (roles { s with rg := Function.update s.rg x (2 * s.rg x % 2 ^ W), fl := decide (2 ^ W ≤ 2 * s.rg x) }) := by
  have h := shl_at (W := W) (roles s) RL (rs x) ZR FL (d4z x) (s.rg x) 0 s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_ZR s) (roles_FL s) ha
  rw [upd_rs, upd_FL] at h
  exact h

theorem clr_run (x : Fin NR) (ha : s.rg x < 2 ^ W) :
    LRuns W (mClr (NO := NO) x) (2 * W + 3) (roles s) (roles { s with fl := false }) := by
  have h := add_at (W := W) (roles s) RL (rs x) ZR FL (d4z x) (s.rg x) 0 s.fl
    (by rw [roles_RL, hr]) (roles_rs s x) (roles_ZR s) (roles_FL s) ha (Nat.two_pow_pos W) (by omega)
  rw [upd_rs, upd_FL] at h
  refine h.congr_out ?_
  show roles ⟨s.rl, false, Function.update s.rg x (s.rg x + 0), s.ot⟩ = roles ⟨s.rl, false, s.rg, s.ot⟩
  rw [Nat.add_zero, Function.update_eq_self]

theorem mul_run (x y z t m : Fin NR)
    (hinj : Function.Injective ![(RL : Fin (4 + NR + NO)), rs x, rs y, rs z, rs t, rs m, FL, ZR])
    (hy : s.rg y < 2 ^ W) (hxy : s.rg x * s.rg y < 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (mMul (NO := NO) x y z t m) (13 * W * W + 60 * W + 40) (roles s)
      (roles { s with rg := mulRg s.rg z t m (s.rg x * s.rg y), fl := false }) := by
  have h := Mul.at_run (W := W) (roles s) RL (rs x) (rs y) (rs z) (rs t) (rs m) FL ZR hinj (s.rg x) (s.rg y)
    (s.rg z) (s.rg t) (s.rg m) s.fl (by rw [roles_RL, hr]) (roles_rs s x) (roles_rs s y) (roles_rs s z)
    (roles_rs s t) (roles_rs s m) (roles_FL s) (roles_ZR s) hy hxy hW
  rw [upd_rs, upd_rs, upd_rs, upd_FL] at h
  exact h

end Instr

/-! ## Stream instructions -/

section Streams
variable {NR NO : ℕ}

def mReadNat (sm mk : Fin NO) (x : Fin NR) := ReadNat.at5 (RL : Fin (4 + NR + NO)) (os sm) (os mk) UB (rs x)
/-- `flag := stream bit` (no move). -/
def mPeek (sm : Fin NO) := RecoveryFocus.machine ![(os sm : Fin (4 + NR + NO)), FL] peek

def mBit (mk sm : Fin NO) := RecoveryFocus.machine ![(os mk : Fin (4 + NR + NO)), os sm, FL] readBit
def mApp (b : Bool) (o om : Fin NO) := RecoveryFocus.machine ![(os o : Fin (4 + NR + NO)), os om] (sapp b)
def mRew (mk sm : Fin NO) := RecoveryFocus.machine ![(os mk : Fin (4 + NR + NO)), os sm] rewind
def mUnf (src sm mk : Fin NO) := RecoveryFocus.machine ![(os src : Fin (4 + NR + NO)), os sm, os mk] Unframe.machine
def mMoveR (k : Fin NO) := RecoveryFocus.machine ![(os k : Fin (4 + NR + NO))] moveR
def mInitOut (o om : Fin NO) :=
  RecoveryFocus.machine ![(os o : Fin (4 + NR + NO)), os om] (oneStep 2 (fun _ => (fun _ => none, fun _ => .right)))

variable {W : ℕ} (s : St NR NO)

theorem readNat_run (hr : s.rl = .ruler) (sm mk : Fin NO) (hne : sm.val ≠ mk.val) (x : Fin NR) (p v : ℕ)
    (f g : ℕ → Bool) (hW : natBitLength v ≤ W)
    (hS : ∀ i, i < (natWord v).length → f (p + i) = (natWord v).getD i false)
    (hs : s.ot sm = .cells f p) (hm : s.ot mk = .cells g p) :
    LRuns W (mReadNat sm mk x) (3 * W + 5) (roles s)
      (roles { s with ot := Function.update (Function.update s.ot sm (.cells f (p + (natWord v).length))) mk (.cells g (p + (natWord v).length)), rg := Function.update s.rg x v }) := by
  have hinj : Function.Injective ![(RL : Fin (4 + NR + NO)), os sm, os mk, UB, rs x] := by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [RL, UB, os, rs] at hv ⊢ <;> omega
  have h := ReadNat.at_run (W := W) (roles s) RL (os sm) (os mk) UB (rs x) hinj p v (s.rg x) f g hW hS
    (by rw [roles_RL, hr]) (by rw [roles_os, hs]) (by rw [roles_os, hm]) (roles_UB s) (roles_rs s x)
  rw [upd_os, upd_os, upd_rs] at h
  exact h

theorem peek_run (sm : Fin NO) (f : ℕ → Bool) (p : ℕ) (hs : s.ot sm = .cells f p) :
    LRuns W (mPeek sm) 1 (roles s) (roles { s with fl := f p }) := by
  have hinj : Function.Injective ![(os sm : Fin (4 + NR + NO)), FL] := by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [FL, os] at hv ⊢ <;> omega
  have h := (peek_lruns W p f s.fl).dockK ![(os sm : Fin (4 + NR + NO)), FL] hinj (roles s)
    (by intro j; fin_cases j
        · exact (roles_os s sm).trans hs
        · exact roles_FL s) [1] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have e : ([1] : List (Fin 2)).foldr (fun k ρ => Function.update ρ ((![(os sm : Fin (4 + NR + NO)), FL] : Fin 2 → Fin (4 + NR + NO)) k)
      ((![.cells f p, .flag (f p)] : Fin 2 → TS) k)) (roles s) = Function.update (roles s) FL (.flag (f p)) := rfl
  rw [e, upd_FL] at h
  exact h

theorem bit_run (mk sm : Fin NO) (hne : mk.val ≠ sm.val) (f g : ℕ → Bool) (p : ℕ) (hs : s.ot sm = .cells f p)
    (hm : s.ot mk = .cells g p) :
    LRuns W (mBit mk sm) 1 (roles s)
      (roles { s with ot := Function.update (Function.update s.ot mk (.cells g (p + 1))) sm (.cells f (p + 1)), fl := f p }) := by
  have hinj : Function.Injective ![(os mk : Fin (4 + NR + NO)), os sm, FL] := by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [FL, os] at hv ⊢ <;> omega
  have h := (readBit_lruns W p f g s.fl).dockK ![(os mk : Fin (4 + NR + NO)), os sm, FL] hinj (roles s)
    (by intro j; fin_cases j
        · exact (roles_os s mk).trans hm
        · exact (roles_os s sm).trans hs
        · exact roles_FL s) [2, 1, 0] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have e : ([2, 1, 0] : List (Fin 3)).foldr (fun k ρ => Function.update ρ
      ((![(os mk : Fin (4 + NR + NO)), os sm, FL] : Fin 3 → Fin (4 + NR + NO)) k)
      ((![.cells g (p + 1), .cells f (p + 1), .flag (f p)] : Fin 3 → TS) k)) (roles s) =
      Function.update (Function.update (Function.update (roles s) (os mk) (.cells g (p + 1))) (os sm)
        (.cells f (p + 1))) FL (.flag (f p)) := rfl
  rw [e, upd_os, upd_os, upd_FL] at h
  exact h

theorem app_run (b : Bool) (o om : Fin NO) (hne : o.val ≠ om.val) (w : List Bool) (ho : s.ot o = sS w)
    (hm : s.ot om = sM w) :
    LRuns W (mApp b o om) 1 (roles s)
      (roles { s with ot := Function.update (Function.update s.ot o (sS (w ++ [b]))) om (sM (w ++ [b])) }) := by
  have hinj : Function.Injective ![(os o : Fin (4 + NR + NO)), os om] := by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [os] at hv ⊢ <;> omega
  have h := (sapp_lruns W b w).dockK ![(os o : Fin (4 + NR + NO)), os om] hinj (roles s)
    (by intro j; fin_cases j
        · exact (roles_os s o).trans ho
        · exact (roles_os s om).trans hm) [1, 0] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have e : ([1, 0] : List (Fin 2)).foldr (fun k ρ => Function.update ρ
      ((![(os o : Fin (4 + NR + NO)), os om] : Fin 2 → Fin (4 + NR + NO)) k)
      ((![sS (w ++ [b]), sM (w ++ [b])] : Fin 2 → TS) k)) (roles s) =
      Function.update (Function.update (roles s) (os o) (sS (w ++ [b]))) (os om) (sM (w ++ [b])) := rfl
  rw [e, upd_os, upd_os] at h
  exact h

theorem rew_run (mk sm : Fin NO) (hne : mk.val ≠ sm.val) (n p : ℕ) (f : ℕ → Bool) (hp1 : 1 ≤ p) (hp : p ≤ n + 1)
    (hm : s.ot mk = .cells (sf (List.replicate n true)) p) (hs : s.ot sm = .cells f p) :
    LRuns W (mRew mk sm) (p + 4) (roles s)
      (roles { s with ot := Function.update (Function.update s.ot mk (.cells (sf (List.replicate n true)) 1)) sm (.cells f 1) }) := by
  have hinj : Function.Injective ![(os mk : Fin (4 + NR + NO)), os sm] := by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [os] at hv ⊢ <;> omega
  have h := (rewind_lruns W n p f hp1 hp).dockK ![(os mk : Fin (4 + NR + NO)), os sm] hinj (roles s)
    (by intro j; fin_cases j
        · exact (roles_os s mk).trans hm
        · exact (roles_os s sm).trans hs) [1, 0] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have e : ([1, 0] : List (Fin 2)).foldr (fun k ρ => Function.update ρ
      ((![(os mk : Fin (4 + NR + NO)), os sm] : Fin 2 → Fin (4 + NR + NO)) k)
      ((![.cells (sf (List.replicate n true)) 1, .cells f 1] : Fin 2 → TS) k)) (roles s) =
      Function.update (Function.update (roles s) (os mk) (.cells (sf (List.replicate n true)) 1)) (os sm)
        (.cells f 1) := rfl
  rw [e, upd_os, upd_os] at h
  exact h

theorem unf_run (src sm mk : Fin NO) (h1 : src.val ≠ sm.val) (h2 : src.val ≠ mk.val) (h3 : sm.val ≠ mk.val)
    (h : ℕ) (w : List Bool) (fx : ℕ → Bool)
    (hX : ∀ i, i < (RepairOrdinary.frame w).length → fx (h + i) = (RepairOrdinary.frame w).getD i false)
    (hsrc : s.ot src = .cells fx h) (hsm : s.ot sm = .cells blank 0) (hmk : s.ot mk = .cells blank 0) :
    LRuns W (mUnf src sm mk) (5 * w.length + 10) (roles s)
      (roles { s with ot := Function.update (Function.update (Function.update s.ot src (.cells fx (h + (RepairOrdinary.frame w).length))) sm (.cells (sf w) 1)) mk (.cells (sf (List.replicate w.length true)) 1) }) := by
  have hinj : Function.Injective ![(os src : Fin (4 + NR + NO)), os sm, os mk] := by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [os] at hv ⊢ <;> omega
  have hh := (Unframe.lruns W h w fx hX).dockK ![(os src : Fin (4 + NR + NO)), os sm, os mk] hinj (roles s)
    (by intro j; fin_cases j
        · exact (roles_os s src).trans hsrc
        · exact (roles_os s sm).trans hsm
        · exact (roles_os s mk).trans hmk) [2, 1, 0] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have e : ([2, 1, 0] : List (Fin 3)).foldr (fun k ρ => Function.update ρ
      ((![(os src : Fin (4 + NR + NO)), os sm, os mk] : Fin 3 → Fin (4 + NR + NO)) k)
      ((![.cells fx (h + (RepairOrdinary.frame w).length), .cells (sf w) 1,
        .cells (sf (List.replicate w.length true)) 1] : Fin 3 → TS) k)) (roles s) =
      Function.update (Function.update (Function.update (roles s) (os src)
        (.cells fx (h + (RepairOrdinary.frame w).length))) (os sm) (.cells (sf w) 1)) (os mk)
        (.cells (sf (List.replicate w.length true)) 1) := rfl
  rw [e, upd_os, upd_os, upd_os] at hh
  exact hh

theorem moveR_run (k : Fin NO) (f : ℕ → Bool) (h : ℕ) (hk : s.ot k = .cells f h) :
    LRuns W (mMoveR k) 1 (roles s) (roles { s with ot := Function.update s.ot k (.cells f (h + 1)) }) := by
  have hinj : Function.Injective ![(os k : Fin (4 + NR + NO))] := by
    intro i j _
    exact Subsingleton.elim i j
  have hh := (moveR_lruns W h f).dockK ![(os k : Fin (4 + NR + NO))] hinj (roles s)
    (by intro j; fin_cases j; exact (roles_os s k).trans hk) [0] (by intro j hj; fin_cases j; simp at hj)
  have e : ([0] : List (Fin 1)).foldr (fun j ρ => Function.update ρ
      ((![(os k : Fin (4 + NR + NO))] : Fin 1 → Fin (4 + NR + NO)) j) ((![.cells f (h + 1)] : Fin 1 → TS) j))
      (roles s) = Function.update (roles s) (os k) (.cells f (h + 1)) := rfl
  rw [e, upd_os] at hh
  exact hh

theorem initOut_lruns :
    LRuns W (oneStep 2 (fun _ => (fun _ => none, fun _ => .right))) 1 ![.cells blank 0, .cells blank 0]
      ![sS [], sM []] := by
  intro H A hA
  have h0 : H 0 = 0 ∧ ∀ j, readTapeBit (A 0) j = blank j := hA 0
  have h1 : H 1 = 0 ∧ ∀ j, readTapeBit (A 1) j = blank j := hA 1
  have hsf : sf [] = blank := by funext j; cases j <;> rfl
  refine ⟨_, _, oneStep_run 2 _ H A, ?_⟩
  intro i
  fin_cases i
  · refine ⟨by simp [HeadMove.apply, h0.1], fun j => ?_⟩
    simp only [acted]
    rw [hsf]; exact h0.2 j
  · refine ⟨by simp [HeadMove.apply, h1.1], fun j => ?_⟩
    simp only [acted]
    rw [List.length_nil, List.replicate_zero, hsf]; exact h1.2 j

theorem initOut_run (o om : Fin NO) (hne : o.val ≠ om.val) (ho : s.ot o = .cells blank 0)
    (hm : s.ot om = .cells blank 0) :
    LRuns W (mInitOut o om) 1 (roles s)
      (roles { s with ot := Function.update (Function.update s.ot o (sS [])) om (sM []) }) := by
  have hinj : Function.Injective ![(os o : Fin (4 + NR + NO)), os om] := by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [os] at hv ⊢ <;> omega
  have hh := (initOut_lruns (W := W)).dockK ![(os o : Fin (4 + NR + NO)), os om] hinj (roles s)
    (by intro j; fin_cases j
        · exact (roles_os s o).trans ho
        · exact (roles_os s om).trans hm) [1, 0] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have e : ([1, 0] : List (Fin 2)).foldr (fun j ρ => Function.update ρ
      ((![(os o : Fin (4 + NR + NO)), os om] : Fin 2 → Fin (4 + NR + NO)) j)
      ((![sS [], sM []] : Fin 2 → TS) j)) (roles s) =
      Function.update (Function.update (roles s) (os o) (sS [])) (os om) (sM []) := rfl
  rw [e, upd_os, upd_os] at hh
  exact hh

end Streams

end
end NearCubicWires.PacketsKeys.RM

