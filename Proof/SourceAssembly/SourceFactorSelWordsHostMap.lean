import Proof.SourceAssembly.SourceFactorSelWordsLocal

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
noncomputable section

/-- Host values of the shared ports `6..28` and of W's region. -/
def hostV (P0 w tc B Pc wB : Nat) (p : Nat) : Nat :=
  if p < 11 then B + 43 + Pc + (p - 6)
  else if p < 15 then P0 + 378 + (p - 11)
  else if p < 20 then P0 + 393 + w + tc + (p - 15)
  else if p < 22 then P0 + 402 + w + tc + (p - 20)
  else if p < 24 then P0 + 405 + w + tc + (p - 22)
  else if p < 25 then B
  else if p < 26 then P0 + 98
  else if p < 29 then P0 + 224 + (p - 26)
  else wB + (p - 29)

/-- The range decoder. -/
def uH (P0 w tc B Pc wB : Nat) (v : Nat) : Nat :=
  if v < P0 + 224 then 25
  else if v < P0 + 378 then 26 + (v - (P0 + 224))
  else if v < P0 + 393 + w + tc then 11 + (v - (P0 + 378))
  else if v < P0 + 402 + w + tc then 15 + (v - (P0 + 393 + w + tc))
  else if v < P0 + 405 + w + tc then 20 + (v - (P0 + 402 + w + tc))
  else if v < B then 22 + (v - (P0 + 405 + w + tc))
  else if v < wB then 24
  else if v < B + 43 + Pc then 29 + (v - wB)
  else 6 + (v - (B + 43 + Pc))

section dec
variable (P0 w tc B Pc wB N : Nat) (hB : B = P0 + 410 + w + tc) (hwB : B < wB) (hN : wB + (N - 29) ≤ B + 43 + Pc)
include hB hwB hN

theorem uH_hostV (p : Nat) (h6 : 6 ≤ p) (hp : p < N) : uH P0 w tc B Pc wB (hostV P0 w tc B Pc wB p) = p := by
  unfold hostV
  by_cases c1 : p < 11
  · rw [if_pos c1]
    have hc : ¬ (B + 43 + Pc + (p - 6) < P0 + 224) ∧ ¬ (B + 43 + Pc + (p - 6) < P0 + 378) ∧
        ¬ (B + 43 + Pc + (p - 6) < P0 + 393 + w + tc) ∧ ¬ (B + 43 + Pc + (p - 6) < P0 + 402 + w + tc) ∧
        ¬ (B + 43 + Pc + (p - 6) < P0 + 405 + w + tc) ∧ ¬ (B + 43 + Pc + (p - 6) < B) ∧
        ¬ (B + 43 + Pc + (p - 6) < wB) ∧ ¬ (B + 43 + Pc + (p - 6) < B + 43 + Pc) ∧
        6 + (B + 43 + Pc + (p - 6) - (B + 43 + Pc)) = p := by omega
    unfold uH
    rw [if_neg hc.1, if_neg hc.2.1, if_neg hc.2.2.1, if_neg hc.2.2.2.1, if_neg hc.2.2.2.2.1, if_neg hc.2.2.2.2.2.1,
      if_neg hc.2.2.2.2.2.2.1, if_neg hc.2.2.2.2.2.2.2.1]
    exact hc.2.2.2.2.2.2.2.2
  rw [if_neg c1]
  by_cases c2 : p < 15
  · rw [if_pos c2]
    have hc : ¬ (P0 + 378 + (p - 11) < P0 + 224) ∧ ¬ (P0 + 378 + (p - 11) < P0 + 378) ∧
        P0 + 378 + (p - 11) < P0 + 393 + w + tc ∧ 11 + (P0 + 378 + (p - 11) - (P0 + 378)) = p := by omega
    unfold uH
    rw [if_neg hc.1, if_neg hc.2.1, if_pos hc.2.2.1]
    exact hc.2.2.2
  rw [if_neg c2]
  by_cases c3 : p < 20
  · rw [if_pos c3]
    have hc : ¬ (P0 + 393 + w + tc + (p - 15) < P0 + 224) ∧ ¬ (P0 + 393 + w + tc + (p - 15) < P0 + 378) ∧
        ¬ (P0 + 393 + w + tc + (p - 15) < P0 + 393 + w + tc) ∧ P0 + 393 + w + tc + (p - 15) < P0 + 402 + w + tc ∧
        15 + (P0 + 393 + w + tc + (p - 15) - (P0 + 393 + w + tc)) = p := by omega
    unfold uH
    rw [if_neg hc.1, if_neg hc.2.1, if_neg hc.2.2.1, if_pos hc.2.2.2.1]
    exact hc.2.2.2.2
  rw [if_neg c3]
  by_cases c4 : p < 22
  · rw [if_pos c4]
    have hc : ¬ (P0 + 402 + w + tc + (p - 20) < P0 + 224) ∧ ¬ (P0 + 402 + w + tc + (p - 20) < P0 + 378) ∧
        ¬ (P0 + 402 + w + tc + (p - 20) < P0 + 393 + w + tc) ∧ ¬ (P0 + 402 + w + tc + (p - 20) < P0 + 402 + w + tc) ∧
        P0 + 402 + w + tc + (p - 20) < P0 + 405 + w + tc ∧
        20 + (P0 + 402 + w + tc + (p - 20) - (P0 + 402 + w + tc)) = p := by omega
    unfold uH
    rw [if_neg hc.1, if_neg hc.2.1, if_neg hc.2.2.1, if_neg hc.2.2.2.1, if_pos hc.2.2.2.2.1]
    exact hc.2.2.2.2.2
  rw [if_neg c4]
  by_cases c5 : p < 24
  · rw [if_pos c5]
    have hc : ¬ (P0 + 405 + w + tc + (p - 22) < P0 + 224) ∧ ¬ (P0 + 405 + w + tc + (p - 22) < P0 + 378) ∧
        ¬ (P0 + 405 + w + tc + (p - 22) < P0 + 393 + w + tc) ∧ ¬ (P0 + 405 + w + tc + (p - 22) < P0 + 402 + w + tc) ∧
        ¬ (P0 + 405 + w + tc + (p - 22) < P0 + 405 + w + tc) ∧ P0 + 405 + w + tc + (p - 22) < B ∧
        22 + (P0 + 405 + w + tc + (p - 22) - (P0 + 405 + w + tc)) = p := by omega
    unfold uH
    rw [if_neg hc.1, if_neg hc.2.1, if_neg hc.2.2.1, if_neg hc.2.2.2.1, if_neg hc.2.2.2.2.1, if_pos hc.2.2.2.2.2.1]
    exact hc.2.2.2.2.2.2
  rw [if_neg c5]
  by_cases c6 : p < 25
  · rw [if_pos c6]
    have hc : ¬ (B < P0 + 224) ∧ ¬ (B < P0 + 378) ∧ ¬ (B < P0 + 393 + w + tc) ∧ ¬ (B < P0 + 402 + w + tc) ∧
        ¬ (B < P0 + 405 + w + tc) ∧ ¬ (B < B) ∧ B < wB ∧ 24 = p := by omega
    unfold uH
    rw [if_neg hc.1, if_neg hc.2.1, if_neg hc.2.2.1, if_neg hc.2.2.2.1, if_neg hc.2.2.2.2.1, if_neg hc.2.2.2.2.2.1,
      if_pos hc.2.2.2.2.2.2.1]
    exact hc.2.2.2.2.2.2.2
  rw [if_neg c6]
  by_cases c7 : p < 26
  · rw [if_pos c7]
    have hc : P0 + 98 < P0 + 224 ∧ 25 = p := by omega
    unfold uH
    rw [if_pos hc.1]
    exact hc.2
  rw [if_neg c7]
  by_cases c8 : p < 29
  · rw [if_pos c8]
    have hc : ¬ (P0 + 224 + (p - 26) < P0 + 224) ∧ P0 + 224 + (p - 26) < P0 + 378 ∧
        26 + (P0 + 224 + (p - 26) - (P0 + 224)) = p := by omega
    unfold uH
    rw [if_neg hc.1, if_pos hc.2.1]
    exact hc.2.2
  rw [if_neg c8]
  have hc : ¬ (wB + (p - 29) < P0 + 224) ∧ ¬ (wB + (p - 29) < P0 + 378) ∧ ¬ (wB + (p - 29) < P0 + 393 + w + tc) ∧
      ¬ (wB + (p - 29) < P0 + 402 + w + tc) ∧ ¬ (wB + (p - 29) < P0 + 405 + w + tc) ∧ ¬ (wB + (p - 29) < B) ∧
      ¬ (wB + (p - 29) < wB) ∧ wB + (p - 29) < B + 43 + Pc ∧ 29 + (wB + (p - 29) - wB) = p := by omega
  unfold uH
  rw [if_neg hc.1, if_neg hc.2.1, if_neg hc.2.2.1, if_neg hc.2.2.2.1, if_neg hc.2.2.2.2.1, if_neg hc.2.2.2.2.2.1,
    if_neg hc.2.2.2.2.2.2.1, if_pos hc.2.2.2.2.2.2.2.1]
  exact hc.2.2.2.2.2.2.2.2

end dec

/-- The value classes of `hostV` (one characterization, used for the range facts). -/
theorem hostV_cases (P0 w tc B Pc wB p : Nat) (h6 : 6 ≤ p) :
    (p < 11 ∧ hostV P0 w tc B Pc wB p = B + 43 + Pc + (p - 6)) ∨
    (11 ≤ p ∧ p < 29 ∧ (hostV P0 w tc B Pc wB p = P0 + 378 + (p - 11) ∧ p < 15 ∨
      hostV P0 w tc B Pc wB p = P0 + 393 + w + tc + (p - 15) ∧ 15 ≤ p ∧ p < 20 ∨
      hostV P0 w tc B Pc wB p = P0 + 402 + w + tc + (p - 20) ∧ 20 ≤ p ∧ p < 22 ∨
      hostV P0 w tc B Pc wB p = P0 + 405 + w + tc + (p - 22) ∧ 22 ≤ p ∧ p < 24 ∨
      hostV P0 w tc B Pc wB p = B ∧ p = 24 ∨
      hostV P0 w tc B Pc wB p = P0 + 98 ∧ p = 25 ∨
      hostV P0 w tc B Pc wB p = P0 + 224 + (p - 26) ∧ 26 ≤ p)) ∨
    (29 ≤ p ∧ hostV P0 w tc B Pc wB p = wB + (p - 29)) := by
  unfold hostV
  by_cases c1 : p < 11
  · left; exact ⟨c1, by rw [if_pos c1]⟩
  rw [if_neg c1]
  by_cases c8 : p < 29
  · right; left
    refine ⟨by omega, c8, ?_⟩
    by_cases c2 : p < 15
    · left; exact ⟨by rw [if_pos c2], c2⟩
    rw [if_neg c2]
    by_cases c3 : p < 20
    · right; left; exact ⟨by rw [if_pos c3], by omega, c3⟩
    rw [if_neg c3]
    by_cases c4 : p < 22
    · right; right; left; exact ⟨by rw [if_pos c4], by omega, c4⟩
    rw [if_neg c4]
    by_cases c5 : p < 24
    · right; right; right; left; exact ⟨by rw [if_pos c5], by omega, c5⟩
    rw [if_neg c5]
    by_cases c6 : p < 25
    · right; right; right; right; left; exact ⟨by rw [if_pos c6], by omega⟩
    rw [if_neg c6]
    by_cases c7 : p < 26
    · right; right; right; right; right; left; exact ⟨by rw [if_pos c7], by omega⟩
    rw [if_neg c7, if_pos c8]
    right; right; right; right; right; right; exact ⟨rfl, by omega⟩
  · right; right
    refine ⟨by omega, ?_⟩
    have hc : ¬ p < 15 ∧ ¬ p < 20 ∧ ¬ p < 22 ∧ ¬ p < 24 ∧ ¬ p < 25 ∧ ¬ p < 26 := by omega
    rw [if_neg hc.1, if_neg hc.2.1, if_neg hc.2.2.1, if_neg hc.2.2.2.1, if_neg hc.2.2.2.2.1, if_neg hc.2.2.2.2.2,
      if_neg c8]

/-- **The dock.** -/
def wsl {V N : Nat} (src : Fin 6 → Fin V) (P0 w tc B Pc wB : Nat)
    (hV : ∀ p, 6 ≤ p → p < N → hostV P0 w tc B Pc wB p < V) : Fin N → Fin V :=
  fun p => if h : p.val < 6 then src ⟨p.val, h⟩ else ⟨hostV P0 w tc B Pc wB p.val, hV p.val (by omega) p.isLt⟩

section dock
variable {V N : Nat} (src : Fin 6 → Fin V) (P0 w tc B Pc wB : Nat)
  (hV : ∀ p, 6 ≤ p → p < N → hostV P0 w tc B Pc wB p < V)

theorem wsl_src (p : Fin N) (h : p.val < 6) : wsl src P0 w tc B Pc wB hV p = src ⟨p.val, h⟩ := by
  unfold wsl; rw [dif_pos h]

theorem wsl_val (p : Fin N) (h : ¬ p.val < 6) : (wsl src P0 w tc B Pc wB hV p).val = hostV P0 w tc B Pc wB p.val := by
  unfold wsl; rw [dif_neg h]

theorem wsl_inj (hB : B = P0 + 410 + w + tc) (hwB : B < wB) (hN : wB + (N - 29) ≤ B + 43 + Pc)
    (hsrc : Function.Injective src) (gB : Nat) (hgB : B < gB) (hsr : ∀ i, gB ≤ (src i).val ∧ (src i).val < wB) :
    Function.Injective (wsl src P0 w tc B Pc wB hV) := by
  intro x y h
  have hv := congrArg Fin.val h
  by_cases hx : x.val < 6
  · by_cases hy : y.val < 6
    · rw [wsl_src src P0 w tc B Pc wB hV x hx, wsl_src src P0 w tc B Pc wB hV y hy] at h
      have := hsrc h
      exact Fin.ext (by have := congrArg Fin.val this; simpa using this)
    · exfalso
      rw [wsl_src src P0 w tc B Pc wB hV x hx, wsl_val src P0 w tc B Pc wB hV y hy] at hv
      have hs := hsr ⟨x.val, hx⟩
      have hc := hostV_cases P0 w tc B Pc wB y.val (by omega)
      have := y.isLt
      omega
  · by_cases hy : y.val < 6
    · exfalso
      rw [wsl_val src P0 w tc B Pc wB hV x hx, wsl_src src P0 w tc B Pc wB hV y hy] at hv
      have hs := hsr ⟨y.val, hy⟩
      have hc := hostV_cases P0 w tc B Pc wB x.val (by omega)
      have := x.isLt
      omega
    · rw [wsl_val src P0 w tc B Pc wB hV x hx, wsl_val src P0 w tc B Pc wB hV y hy] at hv
      apply Fin.ext
      rw [← uH_hostV P0 w tc B Pc wB N hB hwB hN x.val (by omega) x.isLt,
        ← uH_hostV P0 w tc B Pc wB N hB hwB hN y.val (by omega) y.isLt, hv]

end dock

end
end NearCubicWires.SourceFactorSel.WordsHost

