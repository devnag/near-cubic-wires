import Proof.Packets.PacketsResidualHoles

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsCombine
noncomputable section

/-- The kit-dependent holes, at one common kit shape. -/
def KHoles (a : DecompositionAlgorithm) : Prop :=
  ∃ K : KitShape a, Nonempty (CoordFam a K × SymMeta a K × ThrMeta a K × LowerKit.LowerMeta a K)

/-- The kit-independent holes. -/
def FreeHoles (a : DecompositionAlgorithm) : Prop :=
  Nonempty (PrepFam a × CursorFam a × SetupFam a)

/-- Every hole, from the two groups. -/
def holesOfSplit {a : DecompositionAlgorithm} (hk : KHoles a) (hf : FreeHoles a) : Holes a :=
  let x := Classical.choice (Classical.choose_spec hk)
  let y := Classical.choice hf
  ⟨Classical.choose hk, x.1, x.2.1, x.2.2.1, x.2.2.2, y.1, y.2.1, y.2.2⟩

theorem packetConstruction_of_split (selector : CyclicChoice.Laws)
    (hK : ∀ a, KHoles a) (hF : ∀ a, FreeHoles a) : PacketConstruction selector :=
  packetConstruction_of_holes selector fun a => holesOfSplit (hK a) (hF a)

end

end NearCubicWires.PacketsConstruction.Residual

