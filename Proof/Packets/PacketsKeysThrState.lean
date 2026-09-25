import Proof.Packets.PacketsKeysRMProg

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
noncomputable section

/-- The THR program's state. -/
structure TZ where
  rl : TS
  fl : Bool
  P : ℕ
  A : ℕ
  K : ℕ
  I : ℕ
  X : ℕ
  B : ℕ
  Bm : ℕ
  F : ℕ
  R : ℕ
  M : ℕ
  T : ℕ
  MSK : ℕ
  MT : ℕ
  MM : ℕ
  E : ℕ
  Ep : ℕ
  E2m : ℕ
  Em : ℕ
  Jc : ℕ
  SG : ℕ
  S : Fin 4 → ℕ
  ts : TS
  tm : TS
  os : TS
  om : TS
  js : TS
  jd : TS
  tf : TS
  up1 : TS
  d1 : TS
  up1' : TS
  d1' : TS
  up2 : TS
  d2 : TS
  us : Fin 4 → TS
  ds : Fin 4 → TS
  cc : Fin 8 → TS

def rgv (z : TZ) : Fin 24 → ℕ :=
  ![z.P, z.A, z.K, z.I, z.X, z.B, z.Bm, z.F, z.R, z.M, z.T, z.MSK, z.MT, z.MM, z.E, z.Ep, z.E2m, z.Em, z.Jc, z.SG,
    z.S 0, z.S 1, z.S 2, z.S 3]

def otv (z : TZ) : Fin 29 → TS :=
  ![z.ts, z.tm, z.os, z.om, z.js, z.jd, z.tf, z.up1, z.d1, z.up1', z.d1', z.up2, z.d2,
    z.us 0, z.us 1, z.us 2, z.us 3, z.ds 0, z.ds 1, z.ds 2, z.ds 3,
    z.cc 0, z.cc 1, z.cc 2, z.cc 3, z.cc 4, z.cc 5, z.cc 6, z.cc 7]

def toSt (z : TZ) : St 24 29 := ⟨z.rl, z.fl, rgv z, otv z⟩

/-! ## Register and tape indices -/

abbrev rP : Fin 24 := 0
abbrev rA : Fin 24 := 1
abbrev rK : Fin 24 := 2
abbrev rI : Fin 24 := 3
abbrev rX : Fin 24 := 4
abbrev rB : Fin 24 := 5
abbrev rBm : Fin 24 := 6
abbrev rF : Fin 24 := 7
abbrev rR : Fin 24 := 8
abbrev rM : Fin 24 := 9
abbrev rT : Fin 24 := 10
abbrev rMSK : Fin 24 := 11
abbrev rMT : Fin 24 := 12
abbrev rMM : Fin 24 := 13
abbrev rE : Fin 24 := 14
abbrev rEp : Fin 24 := 15
abbrev rE2m : Fin 24 := 16
abbrev rEm : Fin 24 := 17
abbrev rJc : Fin 24 := 18
abbrev rSG : Fin 24 := 19
def rS (c : Fin 4) : Fin 24 := ⟨20 + c.val, by omega⟩

abbrev oTS : Fin 29 := 0
abbrev oTM : Fin 29 := 1
abbrev oOS : Fin 29 := 2
abbrev oOM : Fin 29 := 3
abbrev oJS : Fin 29 := 4
abbrev oJD : Fin 29 := 5
abbrev oTF : Fin 29 := 6
abbrev oUP1 : Fin 29 := 7
abbrev oD1 : Fin 29 := 8
abbrev oUP1' : Fin 29 := 9
abbrev oD1' : Fin 29 := 10
abbrev oUP2 : Fin 29 := 11
abbrev oD2 : Fin 29 := 12
def oUS (c : Fin 4) : Fin 29 := ⟨13 + c.val, by omega⟩
def oDS (c : Fin 4) : Fin 29 := ⟨17 + c.val, by omega⟩
def ocs (c : Fin 4) : Fin 29 := ⟨21 + 2 * c.val, by omega⟩
def ocm (c : Fin 4) : Fin 29 := ⟨22 + 2 * c.val, by omega⟩
def cs (c : Fin 4) : Fin 8 := ⟨2 * c.val, by omega⟩
def cm (c : Fin 4) : Fin 8 := ⟨2 * c.val + 1, by omega⟩

/-! ## Setters: one field is one `Function.update` -/

section Setters
variable (z : TZ) (v : ℕ) (t : TS)

theorem set_A : Function.update (rgv z) rA v = rgv { z with A := v } := by funext i; fin_cases i <;> rfl
theorem set_K : Function.update (rgv z) rK v = rgv { z with K := v } := by funext i; fin_cases i <;> rfl
theorem set_I : Function.update (rgv z) rI v = rgv { z with I := v } := by funext i; fin_cases i <;> rfl
theorem set_X : Function.update (rgv z) rX v = rgv { z with X := v } := by funext i; fin_cases i <;> rfl
theorem set_B : Function.update (rgv z) rB v = rgv { z with B := v } := by funext i; fin_cases i <;> rfl
theorem set_Bm : Function.update (rgv z) rBm v = rgv { z with Bm := v } := by funext i; fin_cases i <;> rfl
theorem set_F : Function.update (rgv z) rF v = rgv { z with F := v } := by funext i; fin_cases i <;> rfl
theorem set_R : Function.update (rgv z) rR v = rgv { z with R := v } := by funext i; fin_cases i <;> rfl
theorem set_M : Function.update (rgv z) rM v = rgv { z with M := v } := by funext i; fin_cases i <;> rfl
theorem set_T : Function.update (rgv z) rT v = rgv { z with T := v } := by funext i; fin_cases i <;> rfl
theorem set_MSK : Function.update (rgv z) rMSK v = rgv { z with MSK := v } := by funext i; fin_cases i <;> rfl
theorem set_MT : Function.update (rgv z) rMT v = rgv { z with MT := v } := by funext i; fin_cases i <;> rfl
theorem set_MM : Function.update (rgv z) rMM v = rgv { z with MM := v } := by funext i; fin_cases i <;> rfl
theorem set_E : Function.update (rgv z) rE v = rgv { z with E := v } := by funext i; fin_cases i <;> rfl
theorem set_Ep : Function.update (rgv z) rEp v = rgv { z with Ep := v } := by funext i; fin_cases i <;> rfl
theorem set_E2m : Function.update (rgv z) rE2m v = rgv { z with E2m := v } := by funext i; fin_cases i <;> rfl
theorem set_Em : Function.update (rgv z) rEm v = rgv { z with Em := v } := by funext i; fin_cases i <;> rfl
theorem set_Jc : Function.update (rgv z) rJc v = rgv { z with Jc := v } := by funext i; fin_cases i <;> rfl
theorem set_SG : Function.update (rgv z) rSG v = rgv { z with SG := v } := by funext i; fin_cases i <;> rfl
theorem set_P : Function.update (rgv z) rP v = rgv { z with P := v } := by funext i; fin_cases i <;> rfl

theorem set_S (c : Fin 4) : Function.update (rgv z) (rS c) v = rgv { z with S := Function.update z.S c v } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl

theorem oset_ts : Function.update (otv z) oTS t = otv { z with ts := t } := by funext i; fin_cases i <;> rfl
theorem oset_tm : Function.update (otv z) oTM t = otv { z with tm := t } := by funext i; fin_cases i <;> rfl
theorem oset_os : Function.update (otv z) oOS t = otv { z with os := t } := by funext i; fin_cases i <;> rfl
theorem oset_om : Function.update (otv z) oOM t = otv { z with om := t } := by funext i; fin_cases i <;> rfl
theorem oset_js : Function.update (otv z) oJS t = otv { z with js := t } := by funext i; fin_cases i <;> rfl
theorem oset_jd : Function.update (otv z) oJD t = otv { z with jd := t } := by funext i; fin_cases i <;> rfl
theorem oset_tf : Function.update (otv z) oTF t = otv { z with tf := t } := by funext i; fin_cases i <;> rfl
theorem oset_up1 : Function.update (otv z) oUP1 t = otv { z with up1 := t } := by funext i; fin_cases i <;> rfl
theorem oset_d1 : Function.update (otv z) oD1 t = otv { z with d1 := t } := by funext i; fin_cases i <;> rfl
theorem oset_up1' : Function.update (otv z) oUP1' t = otv { z with up1' := t } := by funext i; fin_cases i <;> rfl
theorem oset_d1' : Function.update (otv z) oD1' t = otv { z with d1' := t } := by funext i; fin_cases i <;> rfl
theorem oset_up2 : Function.update (otv z) oUP2 t = otv { z with up2 := t } := by funext i; fin_cases i <;> rfl
theorem oset_d2 : Function.update (otv z) oD2 t = otv { z with d2 := t } := by funext i; fin_cases i <;> rfl

theorem oset_us (c : Fin 4) : Function.update (otv z) (oUS c) t = otv { z with us := Function.update z.us c t } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem oset_ds (c : Fin 4) : Function.update (otv z) (oDS c) t = otv { z with ds := Function.update z.ds c t } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem oset_cs (c : Fin 4) : Function.update (otv z) (ocs c) t = otv { z with cc := Function.update z.cc (cs c) t } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem oset_cm (c : Fin 4) : Function.update (otv z) (ocm c) t = otv { z with cc := Function.update z.cc (cm c) t } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl

theorem get_S (c : Fin 4) : rgv z (rS c) = z.S c := by fin_cases c <;> rfl
theorem get_us (c : Fin 4) : otv z (oUS c) = z.us c := by fin_cases c <;> rfl
theorem get_ds (c : Fin 4) : otv z (oDS c) = z.ds c := by fin_cases c <;> rfl
theorem get_cs (c : Fin 4) : otv z (ocs c) = z.cc (cs c) := by fin_cases c <;> rfl
theorem get_cm (c : Fin 4) : otv z (ocm c) = z.cc (cm c) := by fin_cases c <;> rfl

end Setters

end
end NearCubicWires.PacketsKeys.ThrProg

