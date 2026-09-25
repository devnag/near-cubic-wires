import Proof.Assembly.ActualClause

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal P1TopDown
noncomputable section

theorem header_ne_one {t : Nat} (m offset O F V : Nat) (h : offset + t ≤ m) (i : Fin t) :
    (CloseoutWitness.HeaderDock.slots m offset O F V h i).val ≠ 1 := by
  unfold CloseoutWitness.HeaderDock.slots
  by_cases hF : i.val = F
  · rw [if_pos hF]; show 118 ≠ 1; decide
  rw [if_neg hF]
  by_cases hO : i.val = O
  · rw [if_pos hO]; show 78 ≠ 1; decide
  rw [if_neg hO]
  by_cases h2 : i.val = 2
  · rw [if_pos h2]; show 0 ≠ 1; decide
  rw [if_neg h2]
  by_cases hV : i.val = V
  · rw [if_pos hV]; show 150 ≠ 1; decide
  rw [if_neg hV]
  show 150 + (1 + offset + i.val) ≠ 1
  omega

theorem dock_old_ne_one {m t : Nat} (old : Fin m → Fin t) (x : Fin m) (h : (old x).val ≠ 1) :
    (CloseoutWitness.SupportDock.slots old (x.castAdd 1)).val ≠ 1 := by
  rw [CloseoutWitness.SupportDock.slots_old]; exact h

/-- **The admission cache slot is never tape `1`.** -/
theorem ready_cache_ne_one (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k : Nat) (mode : Bool)
    (i : Fin 19) : (WorkspaceSelectedEntryReady.cache sources p k mode i).val ≠ 1 := by
  unfold WorkspaceSelectedEntryReady.cache CloseoutFinalC10ColdCacheAtAdmission.cacheSlot
    CloseoutWitness.BoundedFamilySupport.slots CloseoutWitness.ColdFamilySupport.cache
  exact dock_old_ne_one _ _ (header_ne_one _ _ _ _ _ _ _)

section body
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat) (mode : Bool)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

/-- The body cache's value (the remap of the admission cache past the entry block). -/
theorem cache_val (i : Fin 19) :
    (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val =
      if (WorkspaceSelectedEntryReady.cache sources p k mode i).val < 2 then (WorkspaceSelectedEntryReady.cache sources p k mode i).val
      else WorkspaceSelectedEntry.size sources k r p.clauseDegree + (WorkspaceSelectedEntryReady.cache sources p k mode i).val - 2 := rfl

/-- **No body cache tape is tape `1`.** -/
theorem cache_ne_one (i : Fin 19) : (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val ≠ 1 := by
  have hp : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
    unfold WorkspaceSelectedEntry.size
    omega
  have h1 := ready_cache_ne_one sources p k mode i
  rw [cache_val]
  by_cases hlt : (WorkspaceSelectedEntryReady.cache sources p k mode i).val < 2
  · rw [if_pos hlt]; exact h1
  · rw [if_neg hlt]; omega

/-- Every body cache tape lies below `offset`. -/
theorem cache_lt_offset (i : Fin 19) :
    (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r := by
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have hp : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
    unfold WorkspaceSelectedEntry.size
    omega
  have hc := (WorkspaceSelectedEntryReady.cache sources p k mode i).isLt
  rw [cache_val]
  dsimp only [PCJda54a286946142d3_BranchPhases.offset]
  by_cases hlt : (WorkspaceSelectedEntryReady.cache sources p k mode i).val < 2
  · rw [if_pos hlt]; omega
  · rw [if_neg hlt]; omega

/-- **The dock's six distinctness premises at S's cache and terminal**, for any tape map that keeps the body values. -/
theorem distinct_of_body {V F : Nat} (cacheT : Fin 19 → Fin V) (terminal : Fin V)
    (hcv : ∀ j, (cacheT j).val = (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode j).val)
    (htv : terminal.val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 53)
    (hFo : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ F) :
    Function.Injective cacheT ∧ (∀ j, (cacheT j).val < F) ∧ terminal.val < F ∧ (∀ j, (cacheT j).val ≠ 1) ∧
      (∀ j, cacheT j ≠ terminal) ∧ terminal.val ≠ 1 := by
  have hoff := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    apply PCJ30aa6f1b7c2a4221_.Selected.cache_injective sources p k r scratch mode
    apply Fin.ext
    rw [← hcv i, ← hcv j, h]
  · intro j
    have := cache_lt_offset sources p k r scratch mode j
    rw [hcv j]; omega
  · rw [htv]; omega
  · intro j; rw [hcv j]; exact cache_ne_one sources p k r scratch mode j
  · intro j h
    apply PCJ30aa6f1b7c2a4221_.Selected.cache_ne_terminal sources p k r scratch mode j
    apply Fin.ext
    rw [← hcv j, h, htv]
    rfl
  · rw [htv]; omega

end body

end
end NearCubicWires.SourceRequest.SelLocal

