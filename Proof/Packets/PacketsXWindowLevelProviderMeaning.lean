import Proof.Packets.PacketsXDenseLiteralAtomMeaning
import Proof.Packets.PacketsXVectorDeltaMeaning
import Proof.Packets.PacketsXVectorLiteralDeltaResident
import Proof.Packets.PacketsXWindowLevelProviderLayout

/-! The actual mode counter is the original unmasked hash-child count.
The returned reflected cache is exactly the delta alphabet used by the
concrete window program, so the level output establishes its resident input. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierListPolynomial NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsModeCache VectorBottomUp
noncomputable section

theorem mode_pairs_length (p : Parameters) (M : Nat) : (modePairs p M).length=2*M := by
  simp [modePairs,pairs,two_mul]

theorem level_output_delta_resident (C R population active depth W : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (level : Fin depth) (hd : depth ≤ canonicalGradedRank population active)
    (initial : List PacketVector.Packet) (left right : PacketVector.Packet) (fields : Fin 222 → List Bool)
    (hR : 1 ≤ R) (hready : ProviderReady C R fields)
    (atag : fields 153=WindowSeed.source R (level.val+1))
    (aW : fields 118=WindowSeed.source R W) (au : fields 149=WindowSeed.source R (C+9))
    (aM : fields 150=WindowSeed.source R (2*population))
    (av : fields 151=WindowSeed.source R (Nat.log 2 (2*population)+1))
    (ht : level.val+1+2 ≤ R) (hc : 2*population+2 ≤ R) :
    let p:=parameters population active level.val (C+9) mask seed
    LiteralDeltaResident C R (deltaChildCard (canonicalGradedLabel population active) seed level) W
      (deltaLiteralVariableCodes (population:=population) level)
      (fun j=>levelProviderOutput p population C R initial (providerA C R left right fields) (j.natAdd 34)) := by
  let p:=parameters population active level.val (C+9) mask seed
  let A:=providerA C R left right fields
  let T:=levelProviderOutput p population C R initial A
  have hlen : (modePairs p population).length=2*population := mode_pairs_length p population
  have tag : A 187=WindowSeed.source R (p.level+1) := atag
  have count : A 184=WindowSeed.source R (modePairs p population).length := by rw [hlen];exact aM
  have core : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left right j := fun j=>Fin.addCases_left j
  have kept := (level_output_layout p population C R initial left right A hR core tag count ht (by omega)).2
  have late (i : Fin 256) (hlo : 177 ≤ i.val) (hhi : i.val<188) (h186 : i≠186) : T i=A i := by
    have hn : ¬Workspace.selected i := by unfold Workspace.selected;omega
    have neq (n : Nat) (hn : n<177) (hn256 : n<256) : i≠⟨n,hn256⟩ := by
      intro he;have h:=congrArg Fin.val he;dsimp at h;omega
    dsimp only [T]
    rw [kept i hhi h186 hn (neq 129 (by decide) (by decide)) (neq 140 (by decide) (by decide)),
      mode_output_late p population R _ i (by omega)]
    exact level_input_other R p.level A i (neq 26 (by decide) (by decide)) (neq 27 (by decide) (by decide))
      (neq 159 (by decide) (by decide)) (neq 176 (by decide) (by decide))
  refine ⟨level_output_provider_ready p population C R initial left right fields hR hready tag count ht (by omega),
    ?_,?_,?_,?_,?_,?_⟩
  · change T 150=_
    dsimp only [T]
    rw [kept 150 (by decide) (by decide) (by decide) (by decide) (by decide),mode_child_count]
    rw [original_child_count 2 population active level.val (C+9) mask seed (level.isLt.trans_le hd)]
    rfl
  · change T 152=_
    dsimp only [T]
    rw [kept 152 (by decide) (by decide) (by decide) (by decide) (by decide),
      mode_output_outside p population R _ 152 (by decide),
      level_input_other R p.level A 152 (by decide) (by decide) (by decide) (by decide)]
    exact aW
  · exact (late 183 (by decide) (by decide) (by decide)).trans au
  · change T 184=_
    rw [late 184 (by decide) (by decide) (by decide)]
    simp only [deltaLiteralVariableCodes,List.length_ofFn]
    exact aM
  · change T 185=_
    rw [late 185 (by decide) (by decide) (by decide)]
    simp only [deltaLiteralVariableCodes,List.length_ofFn]
    exact av
  · change T 186=_
    dsimp only [T]
    rw [level_output_cache,hlen,←cache_source]
    rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
