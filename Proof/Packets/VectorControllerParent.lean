import Proof.Packets.VectorControllerData

/-! Exact parent-commit boundaries in the shared provider arena. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorController
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem childSlots_avoid (i : Fin 39) (v : Fin 264) (hv : v.val=257 ∨ v.val=259) : childSlots i≠v := by
  revert hv
  refine Fin.addCases (m:=34) (n:=5) (fun j=>?_) (fun j=>?_) i
  · intro hv he
    rw [childSlots_core] at he
    have he':=congrArg Fin.val he
    simp only [Fin.val_castAdd] at he'
    rcases hv with hv|hv <;>omega
  · intro hv he
    rw [childSlots_extra] at he
    have he':=congrArg Fin.val he
    fin_cases j <;>dsimp at he' <;>rcases hv with hv|hv <;>omega

theorem parentSlots_core (i : Fin 39) : parentSlots (i.castAdd 2)=childSlots i := Fin.addCases_left i
theorem parentSlots_extra (i : Fin 2) : parentSlots (i.natAdd 39)=(![257,259] : Fin 2→Fin 264) i := Fin.addCases_right i

theorem parentSlots_injective : Function.Injective parentSlots := by
  intro i j he
  revert he
  refine Fin.addCases (m:=39) (n:=2) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=39) (n:=2) (fun b=>?_) (fun b=>?_) j
    · intro he
      rw [parentSlots_core,parentSlots_core] at he
      exact congrArg (fun k : Fin 39=>k.castAdd 2) (childSlots_injective he)
    · intro he
      rw [parentSlots_core,parentSlots_extra] at he
      apply False.elim
      exact childSlots_avoid a _ (by fin_cases b <;>simp) he
  · refine Fin.addCases (m:=39) (n:=2) (fun b=>?_) (fun b=>?_) j
    · intro he
      rw [parentSlots_extra,parentSlots_core] at he
      apply False.elim
      exact childSlots_avoid b _ (by fin_cases a <;>simp) he.symm
    · intro he
      rw [parentSlots_extra,parentSlots_extra] at he
      have hi : Function.Injective (![257,259] : Fin 2→Fin 264) := by decide
      exact congrArg (fun k : Fin 2=>k.natAdd 39) (hi he)

theorem parent_heads (mh : Fin 222→Nat) (i : Fin 41) :
    VectorParentCommit.heads i=H mh (parentSlots i) := by
  refine Fin.addCases (m:=39) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [parentSlots_core]
    rw [VectorParentCommit.heads,Fin.addCases_left]
    exact child_heads mh j
  · rw [parentSlots_extra];fin_cases j <;>rfl

theorem parent_tapes (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (i : Fin 41) :
    VectorParentCommit.tapes B R ci pi left right acc previous next i=
      A B R ci pi li left right acc previous next fields (parentSlots i) := by
  refine Fin.addCases (m:=39) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [parentSlots_core]
    rw [VectorParentCommit.tapes,Fin.addCases_left]
    exact child_tapes B R ci pi li left right acc previous next fields j
  · rw [parentSlots_extra];fin_cases j <;>rfl

theorem A_parent_outside (B R ci pi li : Nat) (left right acc acc' : List (List Bool))
    (previous next next' : List Bool) (fields : Fin 222→List Bool) (i : Fin 264) (away : ∀ j,parentSlots j≠i) :
    A B R ci pi li left right acc previous next fields i=A B R ci pi li left right acc' previous next' fields i := by
  revert away
  refine Fin.addCases (m:=256) (n:=8) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=34) (n:=222) (fun k=>?_) (fun k=>?_) j
    · intro _
      have hk : (k.castAdd 222).castAdd 8=k.castAdd 230 := by apply Fin.ext;rfl
      rw [hk,A_core,A_core]
    · intro _;rw [A_meta,A_meta]
  · intro away
    have h1 : j≠1 := by intro he;subst j;exact away 39 rfl
    have h5 : j≠5 := by intro he;subst j;exact away 37 rfl
    have h6 : j≠6 := by intro he;subst j;exact away 38 rfl
    rw [A_extra,A_extra]
    simp only [extraTapes,if_neg h1,if_neg h5,if_neg h6]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorController
