import Proof.Packets.PacketsXWindowLiteralProviderLayout
import Proof.Packets.PacketsXVectorWorkerProviderDock

/-! Reentry invariant for the actual per-child literal provider. It tracks
only allocated work words and the scalar-frame capacities; retained numeric
masters, code cache, and dense atom meanings can be conjoined independently. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def ProviderRetained (j : Fin 222) : Prop := j=91 ∨ j=95 ∨ j=106 ∨ 116 ≤ j.val

structure ProviderReady (C R : Nat) (fields : Fin 222→List Bool) : Prop where
  work : ∀left right i,WindowProvider.Workspace.selected i→(providerA C R left right fields i).length≤R
  seedWords : ∀left right j,(providerA C R left right fields
    (WindowProvider.seedPorts (WindowSeed.privateSlot j))).length≤R
  frame180 : (fields 146).length=R
  frame181 : (fields 147).length=R
  frame182 : (fields 148).length=R

theorem provider_fields_read (C R : Nat) (left right : List (List Bool))
    (T : Fin 256→List Bool) (i : Fin 256) (hi:34 ≤ i.val) :
    providerA C R left right (fun j=>T (j.natAdd 34)) i=T i := by
  revert hi
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · intro hi;have hj:=j.isLt;simp only [Fin.val_castAdd] at hi;omega
  · intro _;simp only [providerA, Fin.addCases_right]

theorem provider_rebuild (C R : Nat) (left right : List (List Bool)) (T : Fin 256→List Bool)
    (hcore:∀j : Fin 34,T (j.castAdd 222)=ReusableArithmetic.state C R left right j) :
    T=providerA C R left right (fun j=>T (j.natAdd 34)) := by
  exact provider_reconstruct C R left right T hcore

theorem provider_scalar_outside (C R : Nat) (left right : List (List Bool))
    (fields fields' : Fin 222→List Bool)
    (he:∀j,j≠146→j≠147→j≠148→fields' j=fields j)
    (i : Fin 256) (h180:i≠180) (h181:i≠181) (h182:i≠182) :
    providerA C R left right fields' i=providerA C R left right fields i := by
  revert h180 h181 h182
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · intro _ _ _;simp only [providerA, Fin.addCases_left]
  · intro h180 h181 h182
    rw [show providerA C R left right fields' (j.natAdd 34)=fields' j from Fin.addCases_right j,
      show providerA C R left right fields (j.natAdd 34)=fields j from Fin.addCases_right j]
    exact he j (by intro hj;subst j;exact h180 rfl)
      (by intro hj;subst j;exact h181 rfl) (by intro hj;subst j;exact h182 rfl)

theorem ready_after_metadata (C R : Nat) (fields fields' : Fin 222→List Bool)
    (h:ProviderReady C R fields)
    (he:∀j,j≠146→j≠147→j≠148→fields' j=fields j)
    (h180:(fields' 146).length=R) (h181:(fields' 147).length=R) (h182:(fields' 148).length=R) :
    ProviderReady C R fields' := by
  refine ⟨?_,?_,h180,h181,h182⟩
  · intro left right i hi
    have hsmall:i.val<150:=by unfold WindowProvider.Workspace.selected at hi;omega
    rw [provider_scalar_outside C R left right fields fields' he i
      (by intro he;subst i;norm_num at hsmall) (by intro he;subst i;norm_num at hsmall)
      (by intro he;subst i;norm_num at hsmall)]
    exact h.work left right i hi
  · intro left right j
    have hsmall:∀j,(WindowProvider.seedPorts (WindowSeed.privateSlot j)).val<96:=by decide
    have hi:=hsmall j
    rw [provider_scalar_outside C R left right fields fields' he _
      (by intro he;rw [he] at hi;norm_num at hi) (by intro he;rw [he] at hi;norm_num at hi)
      (by intro he;rw [he] at hi;norm_num at hi)]
    exact h.seedWords left right j

theorem ready_after_literal (C R v u offset W target : Nat) (codes : List Nat)
    (left : List (List Bool)) (fields : Fin 222→List Bool) (h:ProviderReady C R fields)
    (hu:2*u+1≤R) (hv:2*v+1≤R) (hM:codes.length≤R) (hW:2*W+2≤R)
    (hout:(WindowSeed.emitted v codes.length offset W target).length≤R)
    (hmeta:∀j : Fin 7,providerA C R left [] fields (WindowProvider.seedPorts (j.natAdd 62))=
      WindowSeed.metadata R v u codes.length offset W target j) :
    ProviderReady C R (fun j=>WindowProvider.literalProviderOutput C R v u offset W target codes
      (providerA C R left [] fields) (j.natAdd 34)) := by
  let T:=WindowProvider.literalProviderOutput C R v u offset W target codes (providerA C R left [] fields)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro l r i hi
    have hlarge:34 ≤ i.val:=by unfold WindowProvider.Workspace.selected at hi;omega
    rw [provider_fields_read C R l r T i hlarge]
    dsimp only [T]
    rw [WindowProvider.literal_output_work _ _ _ _ _ _ _ _ _ i hi, List.length_replicate]
  · intro l r j
    have hlarge:∀j,34≤(WindowProvider.seedPorts (WindowSeed.privateSlot j)).val:=by decide
    rw [provider_fields_read C R l r T _ (hlarge j)]
    exact (WindowProvider.literal_output_private C R v u offset W target codes _ hu hv hM hW hout j).le
  · change (T 180).length=R
    dsimp only [T]
    rw [WindowProvider.literal_output_large C R v u offset W target codes _ hmeta 180 (by decide)]
    exact h.frame180
  · change (T 181).length=R
    dsimp only [T]
    rw [WindowProvider.literal_output_large C R v u offset W target codes _ hmeta 181 (by decide)]
    exact h.frame181
  · change (T 182).length=R
    dsimp only [T]
    rw [WindowProvider.literal_output_large C R v u offset W target codes _ hmeta 182 (by decide)]
    exact h.frame182

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
