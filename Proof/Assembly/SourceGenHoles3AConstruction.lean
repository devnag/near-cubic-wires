import Proof.Assembly.SourceGenHoles3Construction
import Proof.SourceAssembly.SourceB
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_2878f47681d7aa799ed6167e.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  (rowConstruction : PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K)
  (maskConstruction : PCJc4297ab269d8423a_Source.MaskConstruction)
  (genHoles3B : NearCubicWires.SourceSkeleton.SourceGenHoles3B selector compiler)
  : (NearCubicWires.SourceSkeleton.SourceGenHoles3A (fun {q m K} => @selector q m K) compiler) :=
  NearCubicWires.SourceSkeleton.genHoles3A_of_B selector compiler genHoles3B
