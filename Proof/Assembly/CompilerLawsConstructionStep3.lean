import Lean
import Proof.Assembly.CompilerLawsConstructionStep2
import Proof.Packets.Ring
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_1ff4ac18b523de3d69f177df.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  : (PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws) :=
  let rowFacts : (
    PCJc06b3608d6d34481_Plan.RowFacts
  ) := (
    PCJc06b3608d6d34481_Rows.rows
  );
  let packetTransport : (
    PCJc06b3608d6d34481_Plan.PacketTransport
  ) := (
    @PCJc06b3608d6d34481_Transport.transport
  );
  (@PCConstruction_41043342827fd64f7b4fa130.parent selector rowFacts packetTransport)
