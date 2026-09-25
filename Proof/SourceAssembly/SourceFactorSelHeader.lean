import Proof.SourceAssembly.SourceRequestFieldPass
import Proof.SourceAssembly.SourceRequestSegments

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Header
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation
noncomputable section

/-- The header's five fields, in order. -/
def fields (mode : Bool) (q L target k : Nat) : Fin 5 → List Bool :=
  ![natWord (if mode then 0 else 1), natWord q, natWord L, natWord target, natWord k]

theorem fields_flatten (mode : Bool) (q L target k : Nat) :
    (List.ofFn (fields mode q L target k)).flatten = SourceRequest.header mode q L target k := by
  simp [fields, SourceRequest.header, List.ofFn_succ, List.append_assoc]

theorem pad_pad (C D : Nat) (w : List Bool) (h : C ≤ D) :
    ZeroPadding.pad D (ZeroPadding.pad C w) = ZeroPadding.pad D w := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc,
    ← List.replicate_add]
  congr 2
  omega

theorem pad_nil (R : Nat) : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by
  simp [ZeroPadding.pad]

/-- The capacities that lift the pass's own entry (`[]` scratch, `c`-cell sources) to blank-backed ports. -/
def caps (Qs : Fin 5 → Nat) (S : Nat) : Fin 11 → Nat :=
  ![Qs 0, Qs 1, Qs 2, Qs 3, Qs 4, S, S, S, S, 0, 0]

/-- The stage's entry on its eleven local ports. -/
def entry (w : Fin 5 → List Bool) (Qs : Fin 5 → Nat) (S R : Nat) : Fin 11 → List Bool :=
  ![ZeroPadding.pad (Qs 0) (frame (w 0)), ZeroPadding.pad (Qs 1) (frame (w 1)),
    ZeroPadding.pad (Qs 2) (frame (w 2)), ZeroPadding.pad (Qs 3) (frame (w 3)),
    ZeroPadding.pad (Qs 4) (frame (w 4)), List.replicate S false, List.replicate S false,
    List.replicate S false, List.replicate S false, List.replicate R false, List.replicate S false]

theorem entry_eq (w : Fin 5 → List Bool) (c : Nat) (Qs : Fin 5 → Nat) (S R : Nat)
    (hcQ : ∀ i, c ≤ Qs i) (hcS : c ≤ S) :
    (fun j => ZeroPadding.pad (caps Qs S j) (SourceRequest.FieldPass.input 5 w c R S j)) = entry w Qs S R := by
  funext j
  fin_cases j
  · exact pad_pad c (Qs 0) _ (hcQ 0)
  · exact pad_pad c (Qs 1) _ (hcQ 1)
  · exact pad_pad c (Qs 2) _ (hcQ 2)
  · exact pad_pad c (Qs 3) _ (hcQ 3)
  · exact pad_pad c (Qs 4) _ (hcQ 4)
  · exact pad_nil S
  · show ZeroPadding.pad S (List.replicate c false) = List.replicate S false
    rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left hcS]
  · exact pad_nil S
  · exact pad_nil S
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _

theorem local_step (w : Fin 5 → List Bool) (c : Nat) (Qs : Fin 5 → Nat) (S R : Nat)
    (hc : ∀ i, 2 * (w i).length + 1 ≤ c) (hcQ : ∀ i, c ≤ Qs i) (hcS : c ≤ S)
    (hL : 2 * (List.ofFn w).flatten.length + 1 ≤ S) :
    ∃ E' : Fin 11 → List Bool,
      Step (SourceRequest.FieldPass.machine 5) (SourceRequest.FieldPass.cost 5 w) (fun _ => 0)
        (entry w Qs S R) (fun _ => 0) E' ∧
      E' 9 = ZeroPadding.pad R (frame (List.ofFn w).flatten) ∧
      (∀ i : Fin 5, E' ⟨i.val, by omega⟩ = ZeroPadding.pad (Qs i) (frame (w i))) := by
  obtain ⟨A', hs, _, _, hdst, hsrc, _, _⟩ := SourceRequest.FieldPass.pass_step 5 w c R S hc hL
  have hp := hs.pad (caps Qs S)
  rw [entry_eq w c Qs S R hcQ hcS] at hp
  refine ⟨_, hp, ?_, ?_⟩
  · show ZeroPadding.pad 0 (A' (SourceRequest.FieldPass.dstP 5)) = _
    rw [hdst, ZeroPadding.pad_zero]
  · intro i
    have e : (⟨i.val, by omega⟩ : Fin 11) = SourceRequest.FieldPass.srcP 5 i := Fin.ext rfl
    have hcap : caps Qs S (SourceRequest.FieldPass.srcP 5 i) = Qs i := by fin_cases i <;> rfl
    rw [e, hcap, hsrc i]
    exact pad_pad c (Qs i) _ (hcQ i)

/-- The docked header machine. -/
def stage {U : Nat} (sl : Fin 11 → Fin U) := RecoveryFocus.machine sl (SourceRequest.FieldPass.machine 5)

theorem stage_step {U : Nat} (sl : Fin 11 → Fin U) (hsl : Function.Injective sl)
    (mode : Bool) (q L target k c S R : Nat) (Qs : Fin 5 → Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hsrc : ∀ i : Fin 5, A (sl ⟨i.val, by omega⟩) = ZeroPadding.pad (Qs i) (frame (fields mode q L target k i)))
    (h5 : A (sl 5) = List.replicate S false) (h6 : A (sl 6) = List.replicate S false)
    (h7 : A (sl 7) = List.replicate S false) (h8 : A (sl 8) = List.replicate S false)
    (h9 : A (sl 9) = List.replicate R false) (h10 : A (sl 10) = List.replicate S false)
    (hc : ∀ i, 2 * (fields mode q L target k i).length + 1 ≤ c) (hcQ : ∀ i, c ≤ Qs i) (hcS : c ≤ S)
    (hL : 2 * (SourceRequest.header mode q L target k).length + 1 ≤ S) :
    ∃ A' : Fin U → List Bool,
      Step (stage sl) (SourceRequest.FieldPass.cost 5 (fields mode q L target k)) H A H A' ∧
      A' (sl 9) = ZeroPadding.pad R (frame (SourceRequest.header mode q L target k)) ∧
      (∀ i : Fin 5, A' (sl ⟨i.val, by omega⟩) = A (sl ⟨i.val, by omega⟩)) ∧
      (∀ x, (∀ j, sl j ≠ x) → A' x = A x) := by
  obtain ⟨E', hs, h9', hsrc'⟩ := local_step (fields mode q L target k) c Qs S R hc hcQ hcS
    (by rw [fields_flatten]; exact hL)
  have hA : ∀ j, A (sl j) = entry (fields mode q L target k) Qs S R j := by
    intro j
    fin_cases j
    · exact hsrc 0
    · exact hsrc 1
    · exact hsrc 2
    · exact hsrc 3
    · exact hsrc 4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10
  have d := hs.dock sl hsl H A (fun j => hH j) hA
  rw [dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_, ?_⟩
  · rw [install_slot sl hsl, h9', fields_flatten]
  · intro i
    rw [install_slot sl hsl, hsrc' i, hsrc i]
  · intro x hx
    exact install_other sl A E' x hx


end
end NearCubicWires.SourceFactorSel.Header
