import Proof.Packets.PacketsCombineThrWord
import Proof.Packets.PacketsKeysPowStage

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsCombine.Asm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsMeta
noncomputable section

/-- The three inputs of the power program: `x` on tape 0, `e` on tape 1, the width `w` on tape 2. -/
def powIns (x : ℕ × ℕ × ℕ) (i : Fin 3) : List Bool :=
  List.replicate (if i.val = 0 then x.1 else if i.val = 1 then x.2.1 else x.2.2) true

/-- The program's side conditions. -/
def powPre (x : ℕ × ℕ × ℕ) : Prop :=
  x.1 < 2 ^ x.2.2 ∧ x.2.1 < 2 ^ x.2.2 ∧ x.1 ^ x.2.1 < 2 ^ x.2.2 ∧ 1 ≤ x.2.2

def Op.pow : Op 3 (ℕ × ℕ × ℕ) powIns (fun x => List.replicate (x.1 ^ x.2.1) true) powPre where
  extra := 13
  states := _
  machine := MaskedReset.machine PacketsKeys.Pow.prog (fun _ => true)
  cost := fun x => 2 * PacketsKeys.Pow.pcost x.1 x.2.1 x.2.2 + 2
  run := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    obtain ⟨s, hl, hout⟩ := PacketsKeys.Pow.prog_run x.1 x.2.1 x.2.2 h1 h2 h3 h4
    have htr : ∀ j : Fin 16, TR x.2.2 (PacketsKeys.Pow.pv x.1 x.2.1 x.2.2 PacketsKeys.Pow.s0 j) 0
        (opIn 3 16 (powIns x) j) := by
      intro j
      by_cases hj : j.val < 3
      · rw [opIn, dif_pos hj]
        have e : powIns x ⟨j.val, hj⟩ =
            List.replicate (if j.val = 2 then x.2.2 else if j.val = 1 then x.2.1 else x.1) true := by
          simp only [powIns]
          congr 1
          split_ifs <;> omega
        rw [e]
        exact PacketsKeys.Pow.tr_in x.2.2 x.1 x.2.1 x.2.2 j hj
      · rw [opIn, dif_neg hj]
        exact PacketsKeys.Pow.tr_nil x.2.2 x.1 x.2.1 x.2.2 j (by omega)
    obtain ⟨H', A', st, hA'⟩ := hl (fun _ => 0) (opIn 3 16 (powIns x)) htr
    obtain ⟨kk, hm⟩ := step_mask0 st (fun _ => true) (by intro i _; rfl)
    have e3 : (⟨3, by omega⟩ : Fin (3 + 1 + 13)) = Fin.castAdd 1 (⟨3, by omega⟩ : Fin 16) := rfl
    have hT := hA' ⟨3, by omega⟩
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.addCases_left]
      · rw [Fin.addCases_right]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.addCases_left]
        simp only [opIn, Fin.val_castAdd]
      · rw [Fin.addCases_right, opIn, dif_neg (by simp only [Fin.val_natAdd]; omega)]
    · rw [e3, Fin.addCases_left, hT.2, hout]
    · rw [e3, Fin.addCases_left]
      simp

/-- `Pow.prog`'s step count is a cubic in `x + e + w + x^e`. -/
theorem pcost_le (x e w : ℕ) : PacketsKeys.Pow.pcost x e w ≤ 512 * (x + e + w + x ^ e + 1) ^ 3 := by
  have hx : x ≤ x + e + w + x ^ e + 1 := by omega
  have he : e ≤ x + e + w + x ^ e + 1 := by omega
  have hw : w ≤ x + e + w + x ^ e + 1 := by omega
  have hp : x ^ e ≤ x + e + w + x ^ e + 1 := by omega
  have h1 : 1 ≤ x + e + w + x ^ e + 1 := by omega
  generalize x + e + w + x ^ e + 1 = Y at hx he hw hp h1 ⊢
  calc PacketsKeys.Pow.pcost x e w ≤ 1 + 1 + ((Y + 1) * (1 + 1 + 2) + 1 + ((Y + 3) + 1 + ((Y + 1) * (1 + (2 * Y + 3) + 2) + 1 +
      ((Y + 1) * (1 + (2 * Y + 3) + 2) + 1 + ((2 * Y + 3) + 1 +
      ((Y + 1) * ((2 * Y + 3) + ((13 * Y * Y + 60 * Y + 40) + 1 + ((2 * Y + 3) + 1 + (2 * Y + 3))) + 2) + 1 +
      (Y + 1) * ((2 * Y + 3) + (2 * Y + 3 + 1 + 1) + 2))))))) := by
        unfold PacketsKeys.Pow.pcost
        gcongr
    _ ≤ 512 * Y ^ 3 := by
        have a1 : Y ≤ Y ^ 3 := by
          calc Y = Y ^ 1 := (pow_one Y).symm
            _ ≤ Y ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
        have a2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
        have a3 : 1 ≤ Y ^ 3 := Nat.one_le_pow _ _ h1
        ring_nf
        nlinarith [a1, a2, a3]

variable {a : DecompositionAlgorithm}

/-- **Three words `1^x, 1^e, 1^w`, then `x^e`.** -/
def ThrWord.pow {ux ue uw : TNat a}
    (sx : ThrWord a (fun r four L target k => List.replicate (ux r four L target k) true))
    (se : ThrWord a (fun r four L target k => List.replicate (ue r four L target k) true))
    (sw : ThrWord a (fun r four L target k => List.replicate (uw r four L target k) true))
    (hgood : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target →
      powPre (ux r four L target k, ue r four L target k, uw r four L target k))
    (cB dB : ℕ) (hB : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target →
      2 * PacketsKeys.Pow.pcost (ux r four L target k) (ue r four L target k) (uw r four L target k) + 2 ≤
        cB * ((Request.thr r four L target).smallSize a) ^ dB) :
    ThrWord a (fun r four L target k => List.replicate (ux r four L target k ^ ue r four L target k) true) :=
  ThrWord.ofVecOp ((((ThrVec.nil a (fun _ _ _ _ _ _ => [])).snoc sx).snoc se).snoc sw) Op.pow
    (fun r four L target k => (ux r four L target k, ue r four L target k, uw r four L target k))
    (fun r four L target k _ i => by
      rcases i with ⟨i, hi⟩
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h | h | h <;> subst h <;> simp [powIns])
    hgood cB dB hB

end
end NearCubicWires.PacketsCombine.Asm

