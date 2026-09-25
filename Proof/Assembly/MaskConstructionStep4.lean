import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Proof.Assembly.MaskConstructionStep1
import Proof.Assembly.MaskConstructionStep3
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_53152a91473677c597d4c75d.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  (rowConstruction : PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K)
  : (PCJc4297ab269d8423a_Source.MaskConstruction) :=
  let body : (
    PCJc4297ab269d8423a_Source.MaskConstruction
  ) := (
    @PCConstruction_85b90d0c518044a5767c0f53.parent selector compiler tables semantics packetConstruction rowConstruction
  );
  (@PCConstruction_b00b774e45e98f2603122195.parent selector compiler tables semantics packetConstruction rowConstruction body)
