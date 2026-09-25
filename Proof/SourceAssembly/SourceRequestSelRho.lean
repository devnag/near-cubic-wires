import Proof.SourceAssembly.SourceRequestCurClausePart

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.SelRho
open NearCubicWires NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

/-- The four admissible multipliers. -/
def Small (x : ℚ) : Prop := x = 0 ∨ x = 1 ∨ x = -1 ∨ x = 1 / 2

theorem small_of_opt (σ : Option Sel) (h : ∀ s, σ = some s → s.rho = 1 ∨ s.rho = -1 ∨ s.rho = 1 / 2) :
    Small (rhoOf σ) := by
  cases σ with
  | none => left; rfl
  | some s =>
    rcases h s rfl with e | e | e
    · right; left; simp [rhoOf, e]
    · right; right; left; simp [rhoOf, e]
    · right; right; right; simp [rhoOf, e]

theorem litEntry_rho (neg r : Bool) (i : Nat) : (litEntry neg r i).rho = 1 ∨ (litEntry neg r i).rho = -1 := by
  unfold litEntry; split
  · left; rfl
  · cases neg <;> simp

theorem side_rho (s r : Bool) (J x : Nat) :
    ∀ u, ((penSide s r J)[x]?).map halfSel = some u → u.rho = 1 ∨ u.rho = -1 ∨ u.rho = 1 / 2 := by
  intro u hu
  cases s with
  | true =>
    by_cases h0 : x = 0
    · subst h0; rw [penSys_0] at hu; simp [halfSel] at hu; subst hu; right; right; norm_num
    by_cases h1 : x - 1 < J
    · rw [penSys_1 r J x (by omega) h1] at hu; simp [halfSel] at hu; subst hu; right; left; norm_num
    by_cases h2 : x - (1 + J) < J * J
    · rw [penSys_2 r J x (by omega) h2] at hu; simp [halfSel] at hu; subst hu; right; right; norm_num
    · exfalso
      have hlen : (penSide true r J).length ≤ x := by
        rw [len_penSide]; simp [MonomialSpec.penLen]; omega
      rw [List.getElem?_eq_none hlen] at hu; simp at hu
  | false =>
    by_cases h0 : x < J * J
    · rw [penAux_0 r J x h0] at hu; simp [halfSel] at hu; subst hu; right; right; norm_num
    by_cases h1 : x - J * J < J * J * J
    · rw [penAux_1 r J x (by omega) h1] at hu; simp [halfSel] at hu; subst hu; right; left; norm_num
    by_cases h2 : x - (J * J + J * J * J) < J * J * (J * J)
    · rw [penAux_2 r J x (by omega) h2] at hu; simp [halfSel] at hu; subst hu; right; right; norm_num
    · exfalso
      have hlen : (penSide false r J).length ≤ x := by
        rw [len_penSide]; simp [MonomialSpec.penLen]; omega
      rw [List.getElem?_eq_none hlen] at hu; simp at hu

/-- **Every site record's multiplier is small.** -/
theorem rho_small (ph : Phase) (sL sR nL nR : Bool) (JL JR m : Nat) :
    Small (rhoOf (selAt ph sL sR nL nR JL JR m)) := by
  apply small_of_opt
  intro s hs
  cases ph with
  | moment =>
    by_cases h : m < JL * JL
    · rw [moment_at sL sR nL nR JL JR m h] at hs; cases hs; left; rfl
    · rw [moment_end sL sR nL nR JL JR m (by omega)] at hs; cases hs
  | penalty =>
    by_cases h : m < MonomialSpec.penLen sL JL
    · rw [penalty_left sL sR nL nR JL JR m h] at hs; exact side_rho sL false JL m s hs
    · rw [penalty_right sL sR nL nR JL JR m (by omega)] at hs; exact side_rho sR true JR _ s hs
  | clause =>
    by_cases h1 : m < JL + nL.toNat
    · rw [clause_litL sL sR nL nR JL JR m h1] at hs; cases hs
      rcases litEntry_rho nL false m with e | e
      · left; exact e
      · right; left; exact e
    by_cases h2 : m - (JL + nL.toNat) < JR + nR.toNat
    · rw [clause_litR sL sR nL nR JL JR m (by omega) h2] at hs; cases hs
      rcases litEntry_rho nR true (m - (JL + nL.toNat)) with e | e
      · left; exact e
      · right; left; exact e
    by_cases h3 : m - ((JL + nL.toNat) + (JR + nR.toNat)) < (JL + nL.toNat) * (JR + nR.toNat)
    · rw [clause_cross sL sR nL nR JL JR m (by omega) h3] at hs; cases hs
      simp only [crossEntry]
      rcases litEntry_rho nL false ((m - (JL + nL.toNat + (JR + nR.toNat))) / (JR + nR.toNat)) with e1 | e1 <;>
        rcases litEntry_rho nR true ((m - (JL + nL.toNat + (JR + nR.toNat))) % (JR + nR.toNat)) with e2 | e2 <;>
        rw [e1, e2] <;> norm_num
    · rw [clause_end sL sR nL nR JL JR m (by omega)] at hs; cases hs

/-- The coefficient stage's width premise at `c0 = rhoW = 2`. -/
theorem rho_bits (ph : Phase) (sL sR nL nR : Bool) (JL JR m : Nat) :
    (rhoOf (selAt ph sL sR nL nR JL JR m)).num.natAbs < 2 ^ rhoW ∧
      (rhoOf (selAt ph sL sR nL nR JL JR m)).den < 2 ^ rhoW := by
  have hhalf : (1 / 2 : ℚ) = (2 : ℚ)⁻¹ := by norm_num
  have hn : ((2 : ℚ)⁻¹).num = 1 := Rat.inv_ofNat_num 2
  have hd : ((2 : ℚ)⁻¹).den = 2 := Rat.inv_ofNat_den 2
  rcases rho_small ph sL sR nL nR JL JR m with e | e | e | e <;> rw [e]
  · decide
  · decide
  · decide
  · rw [hhalf, hn, hd]; decide

end NearCubicWires.SourceRequest.SelRho

