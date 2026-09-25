import Proof.Assembly.SourceGenHoles3AConstruction
import Proof.SourceAssembly.SourcePlanC
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_bc40aee9443586642706a5e3.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  (rowConstruction : PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K)
  (maskConstruction : PCJc4297ab269d8423a_Source.MaskConstruction)
  (genHoles3BTarget : NearCubicWires.SourceSkeleton.SourceGenHoles3B selector compiler)
  : (NearCubicWires.SourceSkeleton.SourceGenHoles3B (fun {q m K} => @selector q m K) compiler) :=
  (fun (_ : True) => genHoles3BTarget) SourcePlanHubC.hub
