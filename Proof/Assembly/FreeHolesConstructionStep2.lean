import Proof.Assembly.FreeHolesConstructionStep1
import Proof.Packets.PacketsKeyWords
import Proof.Packets.PacketsCombineThrMetaPG
import Proof.Packets.PacketsCoordFill
import Proof.Packets.PacketsFreeHoles
import Proof.Packets.PacketsSeedKey
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_891f967648e650b00f998ee1.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (kHoles : ∀ (a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm), NearCubicWires.PacketsConstruction.Residual.KHoles a)
  : (∀ (a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm),
  NearCubicWires.PacketsConstruction.Residual.FreeHoles a) :=
  let freeHolesTarget : (
    ∀ a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm, NearCubicWires.PacketsConstruction.Residual.FreeHoles a
  ) := (
    NearCubicWires.PacketsConstruction.Residual.freeHoles
  );
  (@PCConstruction_f45b3eac6531a8510cb1881b.parent selector compiler tables semantics kHoles freeHolesTarget)
