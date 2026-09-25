import Proof.Rows.RowsInitLiveBounds

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.P1Closure
noncomputable section

/-- **Header 15 and Header 282 of the entry Header block**, pinned: `1^b` with `b` the byte length of the pool's
decomposition cache word plus one, and `tape (min degree N)`. -/
theorem common_radix {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L) (g : Packets.Geometry F)
    (layout : Packets.Layout a F g) :
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 15 =
      List.replicate ((exactListWord (NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.childList a
        (Packets.live F) F.occurrences)).length+1) true ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 282 =
      UnaryTemplate.tape (min layout.degree (Packets.pool a F g).length) := by
  unfold PCJ45bee56da9f34d5a_RowState.commonHeader CompactNativeInitialize.input
  refine ⟨?_, ?_⟩
  · rw [show (15 : Fin 440) = CompactNativeInitialize.metadataSlots 3 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · rw [show (282 : Fin 440) = CompactNativeInitialize.metadataSlots 4 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl

/-- The same at the request's own family (`F = r.family a`). -/
theorem common_radix_req (a : DecompositionAlgorithm) (r : Request) (g : Packets.Geometry (r.family a))
    (layout : Packets.Layout a (r.family a) g) :
    PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) g layout 15 =
      List.replicate ((exactListWord (NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.childList a
        (Packets.live (r.family a)) (r.family a).occurrences)).length+1) true ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) g layout 282 =
      UnaryTemplate.tape (min layout.degree (Packets.pool a (r.family a) g).length) :=
  common_radix a (r.family a) g layout

end
end RowsInit
