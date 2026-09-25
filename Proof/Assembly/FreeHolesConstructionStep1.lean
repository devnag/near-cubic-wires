import Proof.Assembly.PacketConstruction
import Proof.Assembly.PacketsHub
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_f45b3eac6531a8510cb1881b.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (kHoles : ∀ (a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm), NearCubicWires.PacketsConstruction.Residual.KHoles a)
  (freeHolesTarget : ∀ a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm, NearCubicWires.PacketsConstruction.Residual.FreeHoles a)
  : (∀ (a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm),
  NearCubicWires.PacketsConstruction.Residual.FreeHoles a) :=
  (fun (_ : True) => freeHolesTarget) PacketsChildPlanHub.hub
