import Proof.Assembly.SourceAssemblyConstructionStep2
import Proof.Rows.ClosureConstantGateReusable
import Proof.Rows.HeaderBudget
import Proof.Packets.PacketsClog
import Proof.SourceAssembly.SourceSkelProt
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_70e90472006370cbbf699f7d.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  (rowConstruction : PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K)
  (maskConstruction : PCJc4297ab269d8423a_Source.MaskConstruction)
  (genHoles3 : NearCubicWires.SourceSkeleton.SourceGenHoles3 selector compiler)
  : (PCJc4297ab269d8423a_Source.RemainingSource (fun {q m K} => @selector q m K) compiler tables semantics) :=
  NearCubicWires.SourceSkeleton.source_of_gen3 selector compiler tables semantics genHoles3
