import Proof.Assembly.RemainingSourceConstruction
import Proof.Packets.PacketsSetup
import Proof.SourceAssembly.SourceA
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_0c81e141587f19110d0d1c5d.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  (rowConstruction : PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K)
  (maskConstruction : PCJc4297ab269d8423a_Source.MaskConstruction)
  (genHoles3A : NearCubicWires.SourceSkeleton.SourceGenHoles3A selector compiler)
  : (NearCubicWires.SourceSkeleton.SourceGenHoles3 (fun {q m K} => @selector q m K) compiler) :=
  NearCubicWires.SourceSkeleton.genHoles3_of_A selector compiler genHoles3A
