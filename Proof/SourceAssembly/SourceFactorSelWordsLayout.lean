import Proof.SourceAssembly.SourceFactorSelWordsDocks

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Words
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-! ## Sizes -/

/-- The local universe size. -/
def nW (w C k : Nat) : Nat := 754 + 2 * w + 2 * C + 2 * k
/-- W's region size in the host (everything from local `29` on). -/
def gwW (w C k : Nat) : Nat := 725 + 2 * w + 2 * C + 2 * k

theorem nW_eq (w C k : Nat) : nW w C k = 29 + gwW w C k := by unfold nW gwW; omega

def o4 (w : Nat) : Nat := 61 + w
def o5 (w C k : Nat) : Nat := 199 + w + C + k
def o6 (w C k : Nat) : Nat := 221 + 2 * w + C + k
def o7 (w C k : Nat) : Nat := 226 + 2 * w + C + k
def o8 (w C k : Nat) : Nat := 731 + 2 * w + 2 * C + 2 * k
def o9 (w C k : Nat) : Nat := 748 + 2 * w + 2 * C + 2 * k
def o10 (w C k : Nat) : Nat := 751 + 2 * w + 2 * C + 2 * k

/-- Unfold every size and close a linear goal. -/
macro "wz" : tactic => `(tactic| (simp only [nW, gwW, o4, o5, o6, o7, o8, o9, o10] at *; omega))

/-! ## The ten stage docks, by value -/

/-- Copies: sources `0..4` ↦ `0 2 5 6 7`; targets `5..11` ↦ `11 12 15 14 19 16 17`; the log `12` ↦ its block. -/
def t1 (j : Nat) : Nat :=
  match j with
  | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 11 | 6 => 12 | 7 => 15 | 8 => 14 | 9 => 19 | 10 => 16 | _ => 17
def v1 (j : Nat) : Nat := if j < 12 then t1 j else 30 + j
/-- Occ: `0 1 2` ↦ `3 4 18`. -/
def t2 (j : Nat) : Nat := match j with | 0 => 3 | 1 => 4 | _ => 18
def v2 (j : Nat) : Nat := if j < 3 then t2 j else 43 + j
/-- LM: `0 2 3 4 5 7` ↦ `19 15 16 17 18 29`. -/
def t3 (j : Nat) : Nat := match j with | 0 => 19 | 1 => 48 | 2 => 15 | 3 => 16 | 4 => 17 | 5 => 18 | 6 => 53 | _ => 29
def v3 (j : Nat) : Nat := if j < 8 then t3 j else 47 + j
/-- Index block: `ixOut = 132+C+4` ↦ `13`; `ixIn j = 132+C+6+j` ↦ `0 2 6 1 29`. -/
def t4 (w C : Nat) (i : Nat) : Nat :=
  match i with | 0 => 13 | 1 => o4 w + (132 + C + 5) | 2 => 0 | 3 => 2 | 4 => 6 | 5 => 1 | _ => 29
def v4 (w C : Nat) (x : Nat) : Nat :=
  if 132 + C + 4 ≤ x ∧ x < 132 + C + 11 then t4 w C (x - (132 + C + 4)) else o4 w + x
/-- Input pass: `0 3 4 5 6 7 9 11 12 13 14 15` ↦ `28 11 12 13 14 20 21 15 16 17 18 19`. -/
def t5 (w C k : Nat) (j : Nat) : Nat :=
  match j with
  | 0 => 28 | 1 => o5 w C k + 1 | 2 => o5 w C k + 2 | 3 => 11 | 4 => 12 | 5 => 13 | 6 => 14 | 7 => 20
  | 8 => o5 w C k + 8 | 9 => 21 | 10 => o5 w C k + 10 | 11 => 15 | 12 => 16 | 13 => 17 | 14 => 18 | _ => 19
def v5 (w C k : Nat) (j : Nat) : Nat := if j < 16 then t5 w C k j else o5 w C k + j
/-- TK: `0 3` ↦ `8 27`. -/
def v6 (w C k : Nat) (j : Nat) : Nat := if j = 0 then 8 else if j = 3 then 27 else o6 w C k + j
/-- Pool block: `plOut 98, 224` ↦ `25 26`; `plX 225, 226` ↦ `27 28`; `plIn j = 132+C+373+j` ↦ `0 2 6 1 29`. -/
def t7 (i : Nat) : Nat := match i with | 0 => 0 | 1 => 2 | 2 => 6 | 3 => 1 | _ => 29
def v7 (w C k p98 p224 : Nat) (x : Nat) : Nat :=
  if x = p98 then 25 else if x = p224 then 26
  else if 132 + C + 225 ≤ x ∧ x < 132 + C + 227 then x - (132 + C + 225) + 27
  else if 132 + C + 373 ≤ x ∧ x < 132 + C + 378 then t7 (x - (132 + C + 373)) else o7 w C k + x
/-- MS: `0 12 15` ↦ `25 26 24`. -/
def v8 (w C k : Nat) (j : Nat) : Nat := if j = 0 then 25 else if j = 12 then 26 else if j = 15 then 24 else o8 w C k + j
/-- The two unframers: `0 1` ↦ `9 22` and `10 23`. -/
def v9 (w C k : Nat) (j : Nat) : Nat := if j = 0 then 9 else if j = 1 then 22 else o9 w C k + j
def v10 (w C k : Nat) (j : Nat) : Nat := if j = 0 then 10 else if j = 1 then 23 else o10 w C k + j

section vals
variable (w C k : Nat)

theorem v1_cases (j : Nat) (hj : j < 13) : v1 j < 30 ∨ v1 j = 30 + j := by
  unfold v1; split_ifs with h
  · left; interval_cases j <;> decide
  · right; rfl
theorem v2_cases (j : Nat) (hj : j < 4) : v2 j < 30 ∨ v2 j = 43 + j := by
  unfold v2; split_ifs with h
  · left; interval_cases j <;> decide
  · right; rfl
theorem v3_cases (j : Nat) : v3 j < 30 ∨ v3 j = 47 + j := by
  unfold v3; split_ifs with h
  · interval_cases j <;> first | (left; decide) | (right; rfl)
  · right; rfl
theorem v4_cases (x : Nat) : v4 w C x < 30 ∨ v4 w C x = o4 w + x := by
  unfold v4; split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    generalize hi : x - (132 + C + 4) = i
    have hi' : i < 7 := by omega
    by_cases h1 : i = 1
    · right
      subst h1
      show o4 w + (132 + C + 5) = o4 w + x
      omega
    · left
      interval_cases i <;> first | (exact absurd rfl h1) | (simp [t4])
  · right; rfl
theorem v5_cases (j : Nat) : v5 w C k j < 30 ∨ v5 w C k j = o5 w C k + j := by
  unfold v5; split_ifs with h
  · interval_cases j <;> first | (left; simp [t5]; done) | (right; simp [t5])
  · right; rfl
theorem v6_cases (j : Nat) : v6 w C k j < 30 ∨ v6 w C k j = o6 w C k + j := by
  unfold v6; split_ifs <;> first | (left; decide) | (right; rfl)
theorem v7_cases (p98 p224 x : Nat) : v7 w C k p98 p224 x < 30 ∨ v7 w C k p98 p224 x = o7 w C k + x := by
  unfold v7; split_ifs with h1 h2 h3 h4
  · left; decide
  · left; decide
  · left; omega
  · left
    have hi : x - (132 + C + 373) < 5 := by omega
    generalize x - (132 + C + 373) = i at hi
    interval_cases i <;> decide
  · right; rfl
theorem v8_cases (j : Nat) : v8 w C k j < 30 ∨ v8 w C k j = o8 w C k + j := by
  unfold v8; split_ifs <;> first | (left; decide) | (right; rfl)
theorem v9_cases (j : Nat) : v9 w C k j < 30 ∨ v9 w C k j = o9 w C k + j := by
  unfold v9; split_ifs <;> first | (left; decide) | (right; rfl)
theorem v10_cases (j : Nat) : v10 w C k j < 30 ∨ v10 w C k j = o10 w C k + j := by
  unfold v10; split_ifs <;> first | (left; decide) | (right; rfl)

end vals

section maps
variable (w C k : Nat)

def m1 : Fin 13 → Fin (nW w C k) := fun j => ⟨v1 j.val, by have := j.isLt; have := v1_cases j.val this; wz⟩
def m2 : Fin 4 → Fin (nW w C k) := fun j => ⟨v2 j.val, by have := j.isLt; have := v2_cases j.val this; wz⟩
def m3 : Fin (9 + (5 + w)) → Fin (nW w C k) := fun j => ⟨v3 j.val, by have := j.isLt; have := v3_cases j.val; wz⟩
def m4 : Fin ((132 + C) + (6 + k)) → Fin (nW w C k) :=
  fun j => ⟨v4 w C j.val, by have := j.isLt; have := v4_cases w C j.val; wz⟩
def m5 : Fin (22 + w) → Fin (nW w C k) := fun j => ⟨v5 w C k j.val, by have := j.isLt; have := v5_cases w C k j.val; wz⟩
def m6 : Fin 5 → Fin (nW w C k) := fun j => ⟨v6 w C k j.val, by have := j.isLt; have := v6_cases w C k j.val; wz⟩
def m7 (p98 p224 : Nat) : Fin ((132 + C) + (373 + k)) → Fin (nW w C k) :=
  fun j => ⟨v7 w C k p98 p224 j.val, by have := j.isLt; have := v7_cases w C k p98 p224 j.val; wz⟩
def m8 : Fin 17 → Fin (nW w C k) := fun j => ⟨v8 w C k j.val, by have := j.isLt; have := v8_cases w C k j.val; wz⟩
def m9 : Fin 3 → Fin (nW w C k) := fun j => ⟨v9 w C k j.val, by have := j.isLt; have := v9_cases w C k j.val; wz⟩
def m10 : Fin 3 → Fin (nW w C k) := fun j => ⟨v10 w C k j.val, by have := j.isLt; have := v10_cases w C k j.val; wz⟩

/-! Injectivity through a left inverse on the shared ports. -/

/-- A value below `30` comes from a single index (the shared ports of each dock are distinct). -/
theorem inj_of {n N o : Nat} (v : Nat → Nat) (m : Fin n → Fin N) (hm : ∀ j, (m j).val = v j.val)
    (hc : ∀ j, j < n → v j < 30 ∨ v j = o + j) (ho : 30 ≤ o)
    (hlow : ∀ i j, i < n → j < n → v i < 30 → v i = v j → i = j) : Function.Injective m := by
  intro x y h
  have hv : v x.val = v y.val := by rw [← hm, ← hm, h]
  apply Fin.ext
  rcases hc x.val x.isLt with h1 | h1
  · exact hlow _ _ x.isLt y.isLt h1 hv
  · rcases hc y.val y.isLt with h2 | h2
    · exact (hlow _ _ y.isLt x.isLt h2 hv.symm).symm
    · omega

/-! Left inverses on the shared ports (`< 30`). -/

def u1 (p : Nat) : Nat :=
  match p with
  | 0 => 0 | 2 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | 11 => 5 | 12 => 6 | 15 => 7 | 14 => 8 | 19 => 9 | 16 => 10 | _ => 11
def u2 (p : Nat) : Nat := match p with | 3 => 0 | 4 => 1 | _ => 2
def u3 (p : Nat) : Nat := match p with | 19 => 0 | 15 => 2 | 16 => 3 | 17 => 4 | 18 => 5 | _ => 7
def u4 (C : Nat) (p : Nat) : Nat := 132 + C + (match p with | 13 => 4 | 0 => 6 | 2 => 7 | 6 => 8 | 1 => 9 | _ => 10)
def u5 (p : Nat) : Nat :=
  match p with
  | 28 => 0 | 11 => 3 | 12 => 4 | 13 => 5 | 14 => 6 | 20 => 7 | 21 => 9 | 15 => 11 | 16 => 12 | 17 => 13 | 18 => 14
  | _ => 15
def u6 (p : Nat) : Nat := if p = 8 then 0 else 3
def u7 (C p98 p224 : Nat) (p : Nat) : Nat :=
  if p = 25 then p98 else if p = 26 then p224 else if p = 27 then 132 + C + 225 else if p = 28 then 132 + C + 226
  else 132 + C + 373 + (match p with | 0 => 0 | 2 => 1 | 6 => 2 | 1 => 3 | _ => 4)
def u8 (p : Nat) : Nat := if p = 25 then 0 else if p = 26 then 12 else 15
def u9 (p : Nat) : Nat := if p = 9 then 0 else 1
def u10 (p : Nat) : Nat := if p = 10 then 0 else 1

theorem inj_of_u {n N o : Nat} (v u : Nat → Nat) (m : Fin n → Fin N) (hm : ∀ j, (m j).val = v j.val)
    (hc : ∀ j, j < n → v j < 30 ∨ v j = o + j) (ho : 30 ≤ o)
    (hu : ∀ i, i < n → v i < 30 → u (v i) = i) : Function.Injective m :=
  inj_of v m hm hc ho (fun i j hi hj h1 h => by
    have e1 := hu i hi h1
    have e2 := hu j hj (h ▸ h1)
    rw [← e1, ← e2, h])

theorem u1_v1 (i : Nat) (hi : i < 13) (h : v1 i < 30) : u1 (v1 i) = i := by
  unfold v1 at h ⊢; split_ifs at h ⊢ with h0
  · interval_cases i <;> rfl
  · omega
theorem u2_v2 (i : Nat) (hi : i < 4) (h : v2 i < 30) : u2 (v2 i) = i := by
  unfold v2 at h ⊢; split_ifs at h ⊢ with h0
  · interval_cases i <;> rfl
  · omega
theorem u3_v3 (i : Nat) (h : v3 i < 30) : u3 (v3 i) = i := by
  unfold v3 at h ⊢; split_ifs at h ⊢ with h0
  · interval_cases i <;> simp_all [t3, u3]
  · omega
theorem u4_t4 (i : Nat) (hi : i < 7) (h1 : i ≠ 1) : u4 C (t4 w C i) = 132 + C + 4 + i := by
  interval_cases i <;> first | (exact absurd rfl h1) | rfl
theorem u4_v4 (x : Nat) (h : v4 w C x < 30) : u4 C (v4 w C x) = x := by
  unfold v4 at h ⊢; split_ifs at h ⊢ with h0
  · obtain ⟨h1, h2⟩ := h0
    generalize hi : x - (132 + C + 4) = i at h ⊢
    have hi' : i < 7 := by omega
    by_cases hi1 : i = 1
    · subst hi1
      exfalso
      revert h
      show ¬ (o4 w + (132 + C + 5) < 30)
      unfold o4; omega
    · rw [u4_t4 w C i hi' hi1]; omega
  · simp only [o4] at h; omega
theorem u5_t5 (i : Nat) (hi : i < 16) (hio : ¬ (i = 1 ∨ i = 2 ∨ i = 8 ∨ i = 10)) : u5 (t5 w C k i) = i := by
  interval_cases i <;> first | (exact absurd (by decide) hio) | rfl
theorem u5_v5 (i : Nat) (h : v5 w C k i < 30) : u5 (v5 w C k i) = i := by
  unfold v5 at h ⊢; split_ifs at h ⊢ with h0
  · by_cases hio : i = 1 ∨ i = 2 ∨ i = 8 ∨ i = 10
    · exfalso
      have e : t5 w C k i = o5 w C k + i := by rcases hio with rfl | rfl | rfl | rfl <;> rfl
      rw [e] at h; unfold o5 at h; omega
    · exact u5_t5 w C k i h0 hio
  · simp only [o5] at h; omega
theorem u6_v6 (i : Nat) (h : v6 w C k i < 30) : u6 (v6 w C k i) = i := by
  unfold v6 at h ⊢; split_ifs at h ⊢ with h0 h3
  · subst h0; rfl
  · subst h3; rfl
  · simp only [o6] at h; omega
theorem u7_v7 (p98 p224 : Nat) (h98 : p98 < 132 + C) (h224 : p224 < 132 + C) (x : Nat)
    (h : v7 w C k p98 p224 x < 30) : u7 C p98 p224 (v7 w C k p98 p224 x) = x := by
  unfold v7 at h ⊢
  by_cases e1 : x = p98
  · rw [if_pos e1]; unfold u7; rw [if_pos rfl, e1]
  rw [if_neg e1] at h ⊢
  by_cases e2 : x = p224
  · rw [if_pos e2]; unfold u7; rw [if_neg (by omega), if_pos rfl, e2]
  rw [if_neg e2] at h ⊢
  by_cases e3 : 132 + C + 225 ≤ x ∧ x < 132 + C + 227
  · rw [if_pos e3]; unfold u7
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases e4 : x = 132 + C + 225
    · rw [if_pos (by omega)]; omega
    · rw [if_neg (by omega), if_pos (by omega)]; omega
  rw [if_neg e3] at h ⊢
  by_cases e5 : 132 + C + 373 ≤ x ∧ x < 132 + C + 378
  · rw [if_pos e5]
    generalize hi : x - (132 + C + 373) = i
    have hi' : i < 5 := by omega
    have hx : x = 132 + C + 373 + i := by omega
    subst hx
    interval_cases i <;> simp [t7, u7]
  · rw [if_neg e5] at h; simp only [o7] at h; omega
theorem u8_v8 (i : Nat) (h : v8 w C k i < 30) : u8 (v8 w C k i) = i := by
  unfold v8 at h ⊢; split_ifs at h ⊢ with h0 h1 h2
  · subst h0; rfl
  · subst h1; rfl
  · subst h2; rfl
  · simp only [o8] at h; omega
theorem u9_v9 (i : Nat) (h : v9 w C k i < 30) : u9 (v9 w C k i) = i := by
  unfold v9 at h ⊢; split_ifs at h ⊢ with h0 h1
  · subst h0; rfl
  · subst h1; rfl
  · simp only [o9] at h; omega
theorem u10_v10 (i : Nat) (h : v10 w C k i < 30) : u10 (v10 w C k i) = i := by
  unfold v10 at h ⊢; split_ifs at h ⊢ with h0 h1
  · subst h0; rfl
  · subst h1; rfl
  · simp only [o10] at h; omega

theorem m1_inj : Function.Injective (m1 w C k) :=
  inj_of_u v1 u1 (m1 w C k) (fun _ => rfl) v1_cases (by omega) u1_v1
theorem m2_inj : Function.Injective (m2 w C k) :=
  inj_of_u v2 u2 (m2 w C k) (fun _ => rfl) v2_cases (by omega) u2_v2
theorem m3_inj : Function.Injective (m3 w C k) :=
  inj_of_u v3 u3 (m3 w C k) (fun _ => rfl) (fun j _ => v3_cases j) (by omega) (fun i _ h => u3_v3 i h)
theorem m4_inj : Function.Injective (m4 w C k) :=
  inj_of_u (v4 w C) (u4 C) (m4 w C k) (fun _ => rfl) (fun j _ => v4_cases w C j) (by simp only [o4]; omega)
    (fun i _ h => u4_v4 w C i h)
theorem m5_inj : Function.Injective (m5 w C k) :=
  inj_of_u (v5 w C k) u5 (m5 w C k) (fun _ => rfl) (fun j _ => v5_cases w C k j) (by simp only [o5]; omega)
    (fun i _ h => u5_v5 w C k i h)
theorem m6_inj : Function.Injective (m6 w C k) :=
  inj_of_u (v6 w C k) u6 (m6 w C k) (fun _ => rfl) (fun j _ => v6_cases w C k j) (by simp only [o6]; omega)
    (fun i _ h => u6_v6 w C k i h)
theorem m7_inj (p98 p224 : Nat) (h98 : p98 < 132 + C) (h224 : p224 < 132 + C) :
    Function.Injective (m7 w C k p98 p224) :=
  inj_of_u (v7 w C k p98 p224) (u7 C p98 p224) (m7 w C k p98 p224) (fun _ => rfl) (fun j _ => v7_cases w C k p98 p224 j)
    (by simp only [o7]; omega) (fun i _ h => u7_v7 w C k p98 p224 h98 h224 i h)
theorem m8_inj : Function.Injective (m8 w C k) :=
  inj_of_u (v8 w C k) u8 (m8 w C k) (fun _ => rfl) (fun j _ => v8_cases w C k j) (by simp only [o8]; omega)
    (fun i _ h => u8_v8 w C k i h)
theorem m9_inj : Function.Injective (m9 w C k) :=
  inj_of_u (v9 w C k) u9 (m9 w C k) (fun _ => rfl) (fun j _ => v9_cases w C k j) (by simp only [o9]; omega)
    (fun i _ h => u9_v9 w C k i h)
theorem m10_inj : Function.Injective (m10 w C k) :=
  inj_of_u (v10 w C k) u10 (m10 w C k) (fun _ => rfl) (fun j _ => v10_cases w C k j) (by simp only [o10]; omega)
    (fun i _ h => u10_v10 w C k i h)
end maps

/-! ## The target words, the producing stage, the bank invariant -/

/-- The (unpadded) word each shared port ends with. -/
def wd (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (p : Nat) : List Bool :=
  if p = 0 then RepairOrdinary.frame r.nativeWord
  else if p = 1 then List.replicate r.nativeWord.length true
  else if p = 2 then RepairOrdinary.frame (r.supportWord a)
  else if p = 3 then r.supportWord a
  else if p = 4 then List.replicate (r.supportWord a).length true
  else if p = 5 then RepairOrdinary.frame (r.topWord a)
  else if p = 6 then RepairOrdinary.frame (List.replicate r.q true)
  else if p = 7 then RepairOrdinary.frame (List.replicate (normalizedLiveCount r.q r.liveScale) true)
  else if p = 8 then UnaryTemplate.tape (maskData a r).K
  else if p = 9 then RepairOrdinary.frame MB
  else if p = 10 then RepairOrdinary.frame (List.replicate MB.length true)
  else if p = 11 then RepairOrdinary.frame r.nativeWord
  else if p = 12 then RepairOrdinary.frame (r.supportWord a)
  else if p = 13 then RepairOrdinary.frame (r.indexWord a)
  else if p = 14 then RepairOrdinary.frame (r.topWord a)
  else if p = 15 then RepairOrdinary.frame (r.supportWord a)
  else if p = 16 then RepairOrdinary.frame (List.replicate r.q true)
  else if p = 17 then RepairOrdinary.frame (List.replicate (normalizedLiveCount r.q r.liveScale) true)
  else if p = 18 then RepairOrdinary.frame (List.replicate (r.family a).occurrences.length true)
  else if p = 19 then RepairOrdinary.frame (List.replicate r.q true)
  else if p = 20 then r.input a
  else if p = 21 then List.replicate (r.input a).length true
  else if p = 22 then MB
  else if p = 23 then List.replicate MB.length true
  else if p = 24 then List.replicate (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length true
  else if p = 25 then BinaryCacheColdRun.input (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) 98
  else if p = 26 then BinaryCacheColdRun.input (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) 224
  else if p = 27 then UnaryTemplate.tape (maskData a r).K
  else if p = 28 then (maskData a r).word
  else if p = 29 then RepairOrdinary.frame (maskData a r).word
  else []

/-- The stage that produces port `p` (`0` = a source), below `30`. -/
def tp (p : Nat) : Nat :=
  match p with
  | 11 => 1 | 12 => 1 | 13 => 4 | 14 => 1 | 15 => 1 | 16 => 1 | 17 => 1 | 18 => 2 | 19 => 1 | 20 => 5
  | 21 => 5 | 22 => 9 | 23 => 10 | 24 => 8 | 25 => 7 | 26 => 7 | 27 => 6 | 28 => 5 | 29 => 3 | _ => 0
def prod (p : Nat) : Nat := if p < 30 then tp p else 0

/-- The expected content of local port `p` after stage `s`. -/
def Gn (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc s p : Nat) : List Bool :=
  ZeroPadding.pad Rc (if prod p ≤ s then wd a r MB p else [])

/-- **The bank invariant after stage `s`**: every shared port and every block from `lo` on holds its expected word, head `0`. -/
def WI {N : Nat} (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc s lo : Nat)
    (E : Fin N → List Bool) (H : Fin N → Nat) : Prop :=
  ∀ x : Fin N, (x.val < 30 ∨ lo ≤ x.val) → E x = Gn a r MB Rc s x.val ∧ H x = 0

theorem wd_high (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (p : Nat) (hp : 30 ≤ p) :
    wd a r MB p = [] := by
  unfold wd
  repeat rw [if_neg (by omega)]

theorem prod_le (p : Nat) : prod p ≤ 10 := by
  unfold prod; split_ifs with h
  · interval_cases p <;> decide
  · decide

theorem Gn_high (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc s p : Nat) (hp : 30 ≤ p) :
    Gn a r MB Rc s p = List.replicate Rc false := by
  unfold Gn
  rw [wd_high a r MB p hp]
  split_ifs <;> exact Item4.pad_nil_blank Rc

theorem Gn_new (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc s p : Nat) (hp : s < prod p) :
    Gn a r MB Rc s p = List.replicate Rc false := by
  unfold Gn
  rw [if_neg (by omega)]
  exact Item4.pad_nil_blank Rc

theorem Gn_old (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc s p : Nat) (hp : prod p ≤ s) :
    Gn a r MB Rc s p = ZeroPadding.pad Rc (wd a r MB p) := by
  unfold Gn
  rw [if_pos hp]

theorem Gn_final (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc p : Nat) :
    Gn a r MB Rc 10 p = ZeroPadding.pad Rc (wd a r MB p) :=
  Gn_old a r MB Rc 10 p (prod_le p)

/-- **One stage of the invariant**: the stage's own ports (`prod p = s + 1`) end with their words and heads `0`; every other
tracked tape is kept. -/
theorem wi_next {N : Nat} {a : DecompositionAlgorithm} {r : Request} {MB : List Bool} {Rc s lo lo' : Nat}
    {E E' : Fin N → List Bool} {H H' : Fin N → Nat}
    (hWI : WI a r MB Rc s lo E H) (hlo : lo ≤ lo')
    (hout : ∀ x : Fin N, x.val < 30 → prod x.val = s + 1 → E' x = ZeroPadding.pad Rc (wd a r MB x.val) ∧ H' x = 0)
    (hkeep : ∀ x : Fin N, (x.val < 30 ∨ lo' ≤ x.val) → ¬ (x.val < 30 ∧ prod x.val = s + 1) →
      E' x = E x ∧ H' x = H x) :
    WI a r MB Rc (s + 1) lo' E' H' := by
  intro x hx
  by_cases ht : x.val < 30 ∧ prod x.val = s + 1
  · obtain ⟨e1, e2⟩ := hout x ht.1 ht.2
    exact ⟨by rw [e1, Gn_old a r MB Rc (s+1) x.val (by omega)], e2⟩
  · obtain ⟨e1, e2⟩ := hkeep x hx ht
    obtain ⟨g1, g2⟩ := hWI x (by omega)
    refine ⟨?_, by rw [e2, g2]⟩
    rw [e1, g1]
    by_cases h30 : x.val < 30
    · unfold Gn
      have hne : prod x.val ≠ s + 1 := fun e => ht ⟨h30, e⟩
      by_cases hle : prod x.val ≤ s
      · rw [if_pos hle, if_pos (by omega)]
      · rw [if_neg hle, if_neg (by omega)]
    · rw [Gn_high a r MB Rc s x.val (by omega), Gn_high a r MB Rc (s+1) x.val (by omega)]

/-- The initial bank satisfies the invariant at stage `0`. -/
theorem wi_zero {N : Nat} (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc : Nat) (E : Fin N → List Bool)
    (hE : ∀ x : Fin N, E x = Gn a r MB Rc 0 x.val) : WI a r MB Rc 0 30 E (fun _ => 0) :=
  fun x _ => ⟨hE x, rfl⟩

end
end NearCubicWires.SourceFactorSel.Words

