import Proof.Packets.PacketsXWindowLevelProvider
import Proof.Packets.PacketsXVectorProviderReady

/-! Returned layouts for the fixed level producer: cumulative atom storage,
literal codes, the arithmetic engine, and the work-word reentry invariant. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache Theorem25Completion.CycleBounds
noncomputable section

theorem level_atoms_retained (C R tag : Nat) (cs : List CloseoutRowsRawPairSeek.Pair)
    (initial : List PacketVector.Packet) (left : PacketVector.Packet) (A : Fin 256 → List Bool)
    (hengine : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left [] j)
    (atag : A 187=WindowSeed.source R tag) (acount : A 184=WindowSeed.source R cs.length)
    (ht : tag+2≤R) (hc : cs.length+2≤R) (i : Fin 256)
    (hi : i.val<188) (h186 : i≠186) (hwork : ¬Workspace.selected i) (h129 : i≠129) (h140 : i≠140) :
    levelAtomsOutput C R tag cs initial A i=A i := by
  rw [level_atoms_outside_work C R tag cs initial A i hwork h129 h140]
  exact cache_retained R tag cs.length A (hengine 32) (hengine 33) (hengine 31) atag acount ht hc i hi h186

theorem level_atoms_work (C R tag : Nat) (cs : List CloseoutRowsRawPairSeek.Pair)
    (initial : List PacketVector.Packet) (A : Fin 256 → List Bool) (i : Fin 256)
    (hi : Workspace.selected i) : levelAtomsOutput C R tag cs initial A i=List.replicate R false := by
  have away : ∀j : Fin 256,Workspace.selected j → j≠129 ∧ j≠140 := by decide
  obtain ⟨h129,h140⟩:=away i hi
  simp only [levelAtomsOutput,denseReady,Function.update_of_ne h129,Function.update_of_ne h140,
    Workspace.cleared,if_pos hi]

theorem level_output_bank (p : Parameters) (M C R : Nat) (initial : List PacketVector.Packet)
    (A : Fin 256 → List Bool) : levelProviderOutput p M C R initial A 140=
      PacketVector.bank R (DenseAtomProgram.table C (p.level+1) (modePairs p M) initial (modePairs p M).length) :=
  level_atoms_bank C R (p.level+1) (modePairs p M) initial (modeOutput p M R (levelProviderInput R p.level A))

theorem level_output_cache (p : Parameters) (M C R : Nat) (initial : List PacketVector.Packet)
    (A : Fin 256 → List Bool) : levelProviderOutput p M C R initial A 186=
      ZeroPadding.pad R (ReflectedLiteralCache.stream (p.level+1) (modePairs p M).length) :=
  level_atoms_cache C R (p.level+1) (modePairs p M) initial (modeOutput p M R (levelProviderInput R p.level A))

theorem level_output_layout (p : Parameters) (M C R : Nat) (initial : List PacketVector.Packet)
    (left right : PacketVector.Packet) (A : Fin 256 → List Bool) (hR : 1≤R)
    (hengine : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left right j)
    (atag : A 187=WindowSeed.source R (p.level+1))
    (acount : A 184=WindowSeed.source R (modePairs p M).length)
    (ht : p.level+1+2≤R) (hc : (modePairs p M).length+2≤R) :
    (∀j : Fin 34,levelProviderOutput p M C R initial A (j.castAdd 222)=ReusableArithmetic.state C R left [] j) ∧
    (∀i : Fin 256,i.val<188 → i≠186 → ¬Workspace.selected i → i≠129 → i≠140 →
      levelProviderOutput p M C R initial A i=modeOutput p M R (levelProviderInput R p.level A) i) := by
  let B:=modeOutput p M R (levelProviderInput R p.level A)
  have engine : ∀j : Fin 34,B (j.castAdd 222)=ReusableArithmetic.state C R left [] j :=
    mode_output_engine p M C R left [] _ (level_input_engine C R p.level left right A hR hengine)
  have tag : B 187=WindowSeed.source R (p.level+1) :=
    (mode_output_late p M R _ 187 (by decide)).trans
      ((level_input_other R p.level A 187 (by decide) (by decide) (by decide) (by decide)).trans atag)
  have count : B 184=WindowSeed.source R (modePairs p M).length :=
    (mode_output_late p M R _ 184 (by decide)).trans
      ((level_input_other R p.level A 184 (by decide) (by decide) (by decide) (by decide)).trans acount)
  exact ⟨level_atoms_core C R (p.level+1) (modePairs p M) initial left B engine tag count ht hc,
    level_atoms_retained C R (p.level+1) (modePairs p M) initial left B engine tag count ht hc⟩

theorem level_output_provider_ready (p : Parameters) (M C R : Nat) (initial : List PacketVector.Packet)
    (left right : PacketVector.Packet) (fields : Fin 222 → List Bool) (hR : 1≤R)
    (hready : VectorBottomUp.ProviderReady C R fields)
    (atag : VectorBottomUp.providerA C R left right fields 187=WindowSeed.source R (p.level+1))
    (acount : VectorBottomUp.providerA C R left right fields 184=WindowSeed.source R (modePairs p M).length)
    (ht : p.level+1+2≤R) (hc : (modePairs p M).length+2≤R) :
    VectorBottomUp.ProviderReady C R (fun j=>levelProviderOutput p M C R initial
      (VectorBottomUp.providerA C R left right fields) (j.natAdd 34)) := by
  let A:=VectorBottomUp.providerA C R left right fields
  let T:=levelProviderOutput p M C R initial A
  have core : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left right j := fun j=>Fin.addCases_left j
  have kept:= (level_output_layout p M C R initial left right A hR core atag acount ht hc).2
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro l r i hi
    have hlarge : 34 ≤ i.val := by unfold Workspace.selected at hi;omega
    rw [VectorBottomUp.provider_fields_read C R l r T i hlarge]
    exact (congrArg List.length (level_atoms_work C R (p.level+1) (modePairs p M) initial _ i hi)).le.trans
      (by simp)
  · intro l r j
    have away : ∀j,34≤(seedPorts (WindowSeed.privateSlot j)).val ∧
      (seedPorts (WindowSeed.privateSlot j)).val<96 ∧
      seedPorts (WindowSeed.privateSlot j)≠186 ∧ ¬Workspace.selected (seedPorts (WindowSeed.privateSlot j)) ∧
      seedPorts (WindowSeed.privateSlot j)≠129 ∧ seedPorts (WindowSeed.privateSlot j)≠140 ∧
      (∀k,modePorts k≠seedPorts (WindowSeed.privateSlot j)) ∧
      seedPorts (WindowSeed.privateSlot j)≠26 ∧ seedPorts (WindowSeed.privateSlot j)≠27 ∧
      seedPorts (WindowSeed.privateSlot j)≠159 ∧ seedPorts (WindowSeed.privateSlot j)≠176 := by decide
    obtain ⟨hlarge,hsmall,h186,hwork,h129,h140,hmode,h26,h27,h159,h176⟩:=away j
    rw [VectorBottomUp.provider_fields_read C R l r T _ hlarge]
    dsimp only [T]
    rw [kept _ (by omega) h186 hwork h129 h140,mode_output_outside p M R _ _ hmode,
      level_input_other R p.level A _ h26 h27 h159 h176]
    exact hready.seedWords left right j
  all_goals
    first
    | change (T 180).length=R
    | change (T 181).length=R
    | change (T 182).length=R
    dsimp only [T]
    rw [kept _ (by decide) (by decide) (by decide) (by decide) (by decide),
      mode_output_late p M R _ _ (by decide),
      level_input_other R p.level A _ (by decide) (by decide) (by decide) (by decide)]
    first | exact hready.frame180 | exact hready.frame181 | exact hready.frame182

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
