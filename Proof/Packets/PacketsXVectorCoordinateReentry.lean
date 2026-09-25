import Proof.Packets.PacketsXVectorLiteralLevelState
import Proof.Packets.PacketsXWindowCoordinateBoundary

/-! The whole-coordinate substitution restores workspace capacities and
retains the dense bank and all protected original-input and scalar masters. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
noncomputable section

def coordinateFields (C R : Nat) (left right newLeft newRight : PacketVector.Packet)
    (fields : Fin 222 → List Bool) : Fin 222 → List Bool := fun j=>
  WindowProvider.operands R newLeft newRight
    (WindowProvider.Workspace.cleared R (providerA C R left right fields)) (j.natAdd 34)

theorem coordinate_fields_ready (C R : Nat) (left right newLeft newRight : PacketVector.Packet)
    (fields : Fin 222 → List Bool) (h : ProviderReady C R fields) :
    ProviderReady C R (coordinateFields C R left right newLeft newRight fields) := by
  let A:=providerA C R left right fields
  let T:=WindowProvider.operands R newLeft newRight (WindowProvider.Workspace.cleared R A)
  have kept (i : Fin 256) (hi : 34≤ i.val) (hn : ¬WindowProvider.Workspace.selected i) : T i=A i :=
    WindowProvider.coordinate_output_retained R newLeft newRight A i hi hn
  change ProviderReady C R (fun j=>T (j.natAdd 34))
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro l r i hi
    have hlarge : 34≤ i.val := by unfold WindowProvider.Workspace.selected at hi;omega
    rw [provider_fields_read C R l r T i hlarge]
    exact (congrArg List.length (WindowProvider.coordinate_output_work R newLeft newRight A i hi)).le.trans (by simp)
  · intro l r j
    have range : ∀j,34≤(WindowProvider.seedPorts (WindowSeed.privateSlot j)).val ∧
        (WindowProvider.seedPorts (WindowSeed.privateSlot j)).val<96 := by decide
    obtain ⟨hlarge,hsmall⟩:=range j
    rw [provider_fields_read C R l r T _ hlarge,kept _ hlarge (by unfold WindowProvider.Workspace.selected;omega)]
    exact h.seedWords left right j
  all_goals
    first
    | change (T 180).length=R
    | change (T 181).length=R
    | change (T 182).length=R
    rw [kept _ (by decide) (by decide)]
    first | exact h.frame180 | exact h.frame181 | exact h.frame182

theorem coordinate_fields_retained (C R : Nat) (left right newLeft newRight : PacketVector.Packet)
    (fields : Fin 222 → List Bool) (j : Fin 222) (hj : ProviderRetained j) :
    coordinateFields C R left right newLeft newRight fields j=fields j := by
  have hlarge : 34≤(j.natAdd 34 : Fin 256).val := by simp
  have outside : ¬WindowProvider.Workspace.selected (j.natAdd 34) := by
    unfold ProviderRetained at hj
    rcases hj with rfl|rfl|rfl|hj
    · decide
    · decide
    · decide
    · unfold WindowProvider.Workspace.selected
      simp only [Fin.val_natAdd]
      omega
  exact (WindowProvider.coordinate_output_retained R newLeft newRight (providerA C R left right fields)
    (j.natAdd 34) hlarge outside).trans (Fin.addCases_right j)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
