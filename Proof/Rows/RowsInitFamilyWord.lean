import Proof.Rows.RowsInitCount
import Proof.Rows.RowsInitLive

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.FamilyWord
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.PacketsGlue.RequestMeta
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
noncomputable section

section Generic
variable {a : DecompositionAlgorithm} {v : Request → ℕ} (s : UnaryStage a v)

/-- The stage's own tapes (and its masked-reset log) are local `0 … 2+extra`. -/
def sA : Fin (2+s.extra+1) → Fin (2+s.extra+1+3) := Fin.castAdd 3

/-- The counter's four tapes: the stage's output `1^v` (local 1) and three fresh tapes. -/
def sW : Fin 4 → Fin (2+s.extra+1+3) :=
  ![⟨1, by omega⟩, ⟨2+s.extra+1, by omega⟩, ⟨2+s.extra+2, by omega⟩, ⟨2+s.extra+3, by omega⟩]

/-- The word tape (the counter's output tape 2). -/
def wordPort : Fin (2+s.extra+1+3) := ⟨2+s.extra+2, by omega⟩

def sB : Fin 1 → Fin (2+s.extra+1+3) := ![wordPort s]

theorem sA_injective : Function.Injective (sA s) := Fin.castAdd_injective _ _

theorem sW_injective : Function.Injective (sW s) := by
  intro x y h
  have hv := congrArg Fin.val h
  fin_cases x <;> fin_cases y <;> first | rfl | (simp [sW] at hv)

theorem sB_injective : Function.Injective (sB s) := by
  intro x y _
  exact Subsingleton.elim x y

/-- **The fixed machine**: stage (masked) ; counter ; bump. -/
def wordMachine :=
  Composition.machine (RecoveryFocus.machine (sA s) (MaskedReset.machine s.machine (fun _ => true)))
    (Composition.machine (RecoveryFocus.machine (sW s) NearCubicWires.RepairSource.ProjectionNormalization.Counter.machine)
      (RecoveryFocus.machine (sB s) RowsInit.bump))

def wordCost (r : Request) : ℕ :=
  (2*s.cost r+2)+1+(NearCubicWires.RepairSource.ProjectionNormalization.Counter.budget (v r)+1+1)

/-- Entry: the framed request on local 0, every other tape blank. -/
def wordIn (w : List Bool) : Fin (2+s.extra+1+3) → List Bool :=
  Fin.addCases (Fin.addCases (m:=2+s.extra) (n:=1) (motive:=fun _=>List Bool) (inBank (2+s.extra) w)
    (fun _ : Fin 1 => [])) (fun _ : Fin 3 => [])

/-- Exit heads: `1` on the word tape, `0` elsewhere. -/
def wordH (i : Fin (2+s.extra+1+3)) : ℕ := if i = wordPort s then 1 else 0

theorem wordIn_sA (w : List Bool) (j : Fin (2+s.extra+1)) :
    wordIn s w (sA s j) = Fin.addCases (m:=2+s.extra) (n:=1) (motive:=fun _=>List Bool) (inBank (2+s.extra) w)
      (fun _ : Fin 1 => []) j := by
  simp only [wordIn, sA, Fin.addCases_left]

theorem wordIn_hi (w : List Bool) (x : Fin (2+s.extra+1+3)) (hx : 2+s.extra+1 ≤ x.val) : wordIn s w x = [] := by
  have e : x = Fin.natAdd (2+s.extra+1) ⟨x.val-(2+s.extra+1), by omega⟩ := Fin.ext (by simp; omega)
  rw [e]
  simp only [wordIn, Fin.addCases_right]

theorem sA_ne_hi (j : Fin (2+s.extra+1)) (x : Fin (2+s.extra+1+3)) (hx : 2+s.extra+1 ≤ x.val) : sA s j ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  simp only [sA, Fin.val_castAdd] at hv
  have := j.isLt
  omega

/-- **I5, generic**: from the framed request to `CompareMachine.word (v r)` (head `1`) on `wordPort s`. -/
theorem word_run (r : Request) : ∃ A : Fin (2+s.extra+1+3) → List Bool,
    Step (wordMachine s) (wordCost s r) (fun _ => 0) (wordIn s (Request.input a r)) (wordH s) A ∧
      A ⟨0, by omega⟩ = frame (Request.input a r) ∧
      A (wordPort s) = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word (v r) := by
  classical
  set w := Request.input a r with hw
  obtain ⟨A1, h1, a10, a11⟩ := stage_masked s r
  have d1 := dock0 h1 (sA s) (sA_injective s) (wordIn s w) (fun j => wordIn_sA s w j)
  set B1 := install (sA s) (wordIn s w) A1 with hB1
  have b1A : ∀ j, B1 (sA s j) = A1 j := fun j => install_slot _ (sA_injective s) _ _ j
  have b1hi : ∀ x : Fin (2+s.extra+1+3), 2+s.extra+1 ≤ x.val → B1 x = [] := by
    intro x hx
    rw [hB1, install_other _ _ _ _ (fun j => sA_ne_hi s j x hx)]
    exact wordIn_hi s w x hx
  obtain ⟨oW, rW, -, w2⟩ := liveCounter_run (v r)
  have d2 := dock0 rW (sW s) (sW_injective s) B1 (by
    intro j
    fin_cases j
    · show B1 (sA s ⟨1, by omega⟩) = _
      rw [b1A, a11]
      rfl
    · exact b1hi _ (by simp [sW])
    · exact b1hi _ (by simp [sW])
    · exact b1hi _ (by simp [sW]))
  set B2 := install (sW s) B1 oW with hB2
  have b2w : B2 (wordPort s) = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word (v r) := by
    show install (sW s) B1 oW (sW s 2) = _
    rw [install_slot _ (sW_injective s), w2]
  have d3 := (bump_run 0 (NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word (v r))).dock (sB s)
    (sB_injective s) (fun _ => 0) B2 (fun _ => rfl) (fun j => by fin_cases j; exact b2w)
  have hH : dockH (sB s) (fun _ : Fin (2+s.extra+1+3) => (0:ℕ)) (fun _ => 0+1) = wordH s := by
    funext x
    by_cases hx : x = wordPort s
    · subst hx
      rw [show wordPort s = sB s 0 from rfl, dockH_slot _ (sB_injective s)]
      simp [wordH, sB]
    · rw [dockH_other _ _ _ _ (fun j he => by fin_cases j; exact hx he.symm)]
      simp [wordH, hx]
  set B3 := install (sB s) B2 (fun _ => NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word (v r))
    with hB3
  refine ⟨B3, (d1.seq (d2.seq (d3.congr hH rfl))), ?_, ?_⟩
  · have n3 : ∀ j, sB s j ≠ ⟨0, by omega⟩ := by
      intro j he
      fin_cases j
      have := congrArg Fin.val he
      simp [sB, wordPort] at this
    have n2 : ∀ j, sW s j ≠ ⟨0, by omega⟩ := by
      intro j he
      have := congrArg Fin.val he
      fin_cases j <;> simp [sW] at this
    rw [hB3, install_other _ _ _ _ n3, hB2, install_other _ _ _ _ n2,
      show (⟨0, by omega⟩ : Fin (2+s.extra+1+3)) = sA s ⟨0, by omega⟩ from rfl, b1A, a10]
  · show install (sB s) B2 _ (sB s 0) = _
    rw [install_slot _ (sB_injective s)]

/-- Cost: the stage's own bound plus a linear term in the value (rowInitBudget's `rows.length` term). -/
theorem wordCost_le (r : Request) :
    wordCost s r ≤ 2 * (s.coefficient * (r.smallSize a) ^ s.degree) + 10 * v r + 18 := by
  have h := s.cost_le r
  unfold wordCost NearCubicWires.RepairSource.ProjectionNormalization.Counter.budget
  omega

/-- Cost as one fixed power of `smallSize` (rowBudget's `smallSize^degree` term). -/
theorem wordCost_small : ∃ c d : ℕ, ∀ r : Request, wordCost s r ≤ c * (r.smallSize a) ^ d := by
  refine ⟨2 * s.coefficient + 10 * (s.coefficient + 7) + 18, s.degree + 1, fun r => ?_⟩
  have h1 := wordCost_le s r
  have h2 := s.value_bound r
  have hs := one_le_small a r
  have p1 : (r.smallSize a) ^ s.degree ≤ (r.smallSize a) ^ (s.degree + 1) := Nat.pow_le_pow_right hs (by omega)
  have p0 : 1 ≤ (r.smallSize a) ^ (s.degree + 1) := Nat.one_le_pow _ _ hs
  have q1 := Nat.mul_le_mul_left s.coefficient p1
  have e : (2 * s.coefficient + 10 * (s.coefficient + 7) + 18) * (r.smallSize a) ^ (s.degree + 1) =
      2 * (s.coefficient * (r.smallSize a) ^ (s.degree + 1)) +
        10 * ((s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1)) + 18 * (r.smallSize a) ^ (s.degree + 1) := by
    ring
  rw [e]
  omega

end Generic

/-! ## At the row count -/

end
end RowsInit.FamilyWord
