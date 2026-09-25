import Proof.Assembly.KHolesConstructionStep1
import Proof.Packets.PacketsFreeHoles
import Proof.MachineModel.BlockPolyBound
import Proof.Rows.CanonicalBaseInput
import Proof.Packets.PacketsKHolesClosed
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_d34d28037761decdb48e39b7.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  : (∀ (a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm), NearCubicWires.PacketsConstruction.Residual.KHoles a) :=
  let kHolesTarget : (
    ∀ a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm, NearCubicWires.PacketsConstruction.Residual.KHoles a
  ) := (
    NearCubicWires.PacketsConstruction.Residual.KH.kHoles
  );
  (@PCConstruction_c0d5c45dc34cf888ba98cf8b.parent selector compiler tables semantics kHolesTarget)
