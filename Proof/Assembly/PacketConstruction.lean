import Proof.Assembly.CachedRecipeConstructionStep2
import Proof.MachineModel.BlockScrubEntry
import Proof.Rows.HeaderBudget
import Proof.SourceAssembly.PoolDonorCompatible
import Proof.Packets.PacketsSetup
import Proof.Packets.PacketsWalk
import Proof.Packets.PacketsMetaBody
import Proof.Packets.PacketsHolesSplit
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_0e3a87699efe11080573df09.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (kHoles : ∀ a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm, NearCubicWires.PacketsConstruction.Residual.KHoles a)
  (freeHoles : ∀ a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm, NearCubicWires.PacketsConstruction.Residual.FreeHoles a)
  : (PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K) :=
  NearCubicWires.PacketsConstruction.Residual.packetConstruction_of_split selector kHoles freeHoles
