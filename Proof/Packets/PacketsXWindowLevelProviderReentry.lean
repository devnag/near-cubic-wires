import Proof.Packets.PacketsXWindowLevelProviderLayout
import Proof.Packets.PacketsXWindowLevelProviderBounded

/-! Concrete returned mode-cache state and scalar retention for the next
level. These are equalities of the actual producer output, including private
backing and the cumulative dense atom table. -/
set_option autoImplicit false
set_option maxHeartbeats 70000
set_option maxRecDepth 1000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
noncomputable section

theorem mode_input_change_level (p : Parameters) (M R level : Nat) (out : List Bool)
    (priv : Fin 15 → List Bool) (i : Fin 29) (hi : i≠12) :
    ModeCacheReady.A {p with level:=level} M R out priv i=ModeCacheReady.A p M R out priv i := by
  fin_cases i <;> simp_all [ModeCacheReady.A,ModeCacheReady.caps,reuseData,Fin.addCases]

theorem level_output_mode (p : Parameters) (M C R : Nat) (initial : List PacketVector.Packet)
    (left right : PacketVector.Packet) (A : Fin 256 → List Bool) (hR : 1≤R)
    (hengine : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left right j)
    (atag : A 187=WindowSeed.source R (p.level+1))
    (acount : A 184=WindowSeed.source R (modePairs p M).length)
    (ht : p.level+3≤R) (hc : (modePairs p M).length+2≤R) (i : Fin 29) :
    levelProviderOutput p M C R initial A (modePorts i)=
      ModeCacheReady.A p M R (ModeCacheReady.word p M) (reuseFinal 2 p M R) i := by
  have away : ∀j,(modePorts j).val<188 ∧ modePorts j≠186 ∧ ¬Workspace.selected (modePorts j) ∧
    modePorts j≠129 ∧ modePorts j≠140 := by decide
  obtain ⟨hlt,h186,hwork,h129,h140⟩:=away i
  rw [(level_output_layout p M C R initial left right A hR hengine atag acount (by omega) hc).2
    _ hlt h186 hwork h129 h140]
  simp only [modeOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot modePorts mode_injective]

theorem level_output_master (p : Parameters) (M C R : Nat) (initial : List PacketVector.Packet)
    (left right : PacketVector.Packet) (A : Fin 256 → List Bool) (hR : 1≤R)
    (hengine : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left right j)
    (atag : A 187=WindowSeed.source R (p.level+1))
    (acount : A 184=WindowSeed.source R (modePairs p M).length)
    (ht : p.level+3≤R) (hc : (modePairs p M).length+2≤R) (i : Fin 256)
    (hi : i=151 ∨ i=152 ∨ i=177 ∨ i=178 ∨ i=179 ∨ i=183 ∨ i=184 ∨ i=185 ∨ i=187) :
    levelProviderOutput p M C R initial A i=A i := by
  have away : ∀j : Fin 256,(j=151 ∨ j=152 ∨ j=177 ∨ j=178 ∨ j=179 ∨ j=183 ∨ j=184 ∨ j=185 ∨ j=187) →
      j.val<188 ∧ j≠186 ∧ ¬Workspace.selected j ∧ j≠129 ∧ j≠140 ∧
      (∀k,modePorts k≠j) ∧ j≠26 ∧ j≠27 ∧ j≠159 ∧ j≠176 := by decide
  obtain ⟨hlt,h186,hwork,h129,h140,hmode,h26,h27,h159,h176⟩:=away i hi
  rw [(level_output_layout p M C R initial left right A hR hengine atag acount (by omega) hc).2
    _ hlt h186 hwork h129 h140,mode_output_outside p M R _ _ hmode,
    level_input_other R p.level A i h26 h27 h159 h176]

theorem level_output_temp (p : Parameters) (M C R : Nat) (initial : List PacketVector.Packet)
    (left right : PacketVector.Packet) (A : Fin 256 → List Bool) (hR : 1≤R)
    (hengine : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left right j)
    (atag : A 187=WindowSeed.source R (p.level+1))
    (acount : A 184=WindowSeed.source R (modePairs p M).length)
    (ht : p.level+3≤R) (hc : (modePairs p M).length+2≤R) :
    levelProviderOutput p M C R initial A 176=List.replicate R false := by
  rw [(level_output_layout p M C R initial left right A hR hengine atag acount (by omega) hc).2
    176 (by decide) (by decide) (by decide) (by decide) (by decide),
    mode_output_late p M R _ 176 (by decide)]
  simp only [levelProviderInput,modeLevelOutput,Function.update_of_ne (by decide : (176 : Fin 256)≠159),Function.update_self]

theorem level_output_count (p : Parameters) (M C R : Nat) (initial : List PacketVector.Packet)
    (left right : PacketVector.Packet) (A : Fin 256 → List Bool) (hR : 1≤R)
    (hengine : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left right j)
    (atag : A 187=WindowSeed.source R (p.level+1))
    (acount : A 184=WindowSeed.source R (modePairs p M).length)
    (ht : p.level+3≤R) (hc : (modePairs p M).length+2≤R) :
    levelProviderOutput p M C R initial A 129=WindowSeed.source R (modePairs p M).length := by
  have h : levelProviderOutput p M C R initial A 129=levelProviderOutput p M C R initial A 184 := rfl
  exact h.trans ((level_output_master p M C R initial left right A hR hengine atag acount ht hc 184 (by decide)).trans acount)

theorem level_output_table_fits (p : Parameters) (M C w : Nat) (initial : List PacketVector.Packet)
    (hr : p.rank≤9*M) (hl : p.level≤p.rank) (hC : (258*M+2)^2≤C) (hw : 1≤w)
    (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P) :
    ∀P∈DenseAtomProgram.table C (p.level+1) (modePairs p M) initial (modePairs p M).length,
      PacketVector.Fits (commonReserve C w) P := by
  have shapes:=(mode_pair_guards C M p hr hl hC).2.2.2
  apply DenseAtomProgram.table_fits C _ _ _ initial hinits _ _ le_rfl
  intro pair hp
  obtain ⟨_,hf,ha,hfuel⟩:=atom_guards C w hw pair (shapes pair hp)
  exact NativeNormalized.output_fits C _ (pair.1++pair.2) hf ha hfuel

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
