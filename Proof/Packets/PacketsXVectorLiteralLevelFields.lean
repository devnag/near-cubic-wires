import Proof.Packets.PacketsXVectorWorkerPrepareRight
import Proof.Packets.PacketsXVectorProviderReady

/-! The level controller changes exactly the resident window and successor
tag. Its paid updates preserve every provider workspace capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

theorem provider_level_fields_other (C R root level : Nat) (left right : PacketVector.Packet)
    (fields : Fin 222 → List Bool) (i : Fin 256) (h152 : i≠152) (h187 : i≠187) :
    providerA C R left right (levelFields R root level fields) i=providerA C R left right fields i := by
  revert h152 h187
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · intro _ _
    simp only [providerA,Fin.addCases_left]
  · intro h152 h187
    have h118 : j≠118 := by intro he;subst j;exact h152 rfl
    have h153 : j≠153 := by intro he;subst j;exact h187 rfl
    simp only [providerA,Fin.addCases_right,levelFields,Function.update_of_ne h118,Function.update_of_ne h153]

theorem ready_level_fields (C R root level : Nat) (fields : Fin 222 → List Bool)
    (h : ProviderReady C R fields) : ProviderReady C R (levelFields R root level fields) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro left right i hi
    have small : i.val<150 := by unfold WindowProvider.Workspace.selected at hi;omega
    rw [provider_level_fields_other C R root level left right fields i
      (by intro he;subst i;norm_num at small) (by intro he;subst i;norm_num at small)]
    exact h.work left right i hi
  · intro left right j
    have away : ∀j,WindowProvider.seedPorts (WindowSeed.privateSlot j)≠152 ∧
        WindowProvider.seedPorts (WindowSeed.privateSlot j)≠187 := by decide
    rw [provider_level_fields_other C R root level left right fields _ (away j).1 (away j).2]
    exact h.seedWords left right j
  · simpa only [levelFields,Function.update_of_ne (by decide : (146 : Fin 222)≠153),
      Function.update_of_ne (by decide : (146 : Fin 222)≠118)] using h.frame180
  · simpa only [levelFields,Function.update_of_ne (by decide : (147 : Fin 222)≠153),
      Function.update_of_ne (by decide : (147 : Fin 222)≠118)] using h.frame181
  · simpa only [levelFields,Function.update_of_ne (by decide : (148 : Fin 222)≠153),
      Function.update_of_ne (by decide : (148 : Fin 222)≠118)] using h.frame182

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
