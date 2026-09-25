import Proof.Assembly.Packets

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SourceInterfaces
open PCJ9eff70d512234a4c_Fixed

namespace PCJc06b3608d6d34481_Plan

def RowFacts : Prop :=
  ∀ (sources : EightSources) (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp))
    (r : Packets.Row (Packets.request sources L target mode atoms).occurrences L),
    r ∈ (Packets.request sources L target mode atoms).rows →
      Ring.Degree r.degree r.polynomial ∧
      ∀ assignment : Nat → Bool,
        evaluateStructuralGF2 assignment r.polynomial =
          evaluateStructuralGF2 assignment r.reference

def PacketTransport : Prop :=
  ∀ {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) (r : Packets.Row F.occurrences L),
    (Ring.Degree r.degree r.polynomial ∧
      ∀ assignment : Nat → Bool,
        evaluateStructuralGF2 assignment r.polynomial =
          evaluateStructuralGF2 assignment r.reference) →
    Packets.PacketFacts a F g r

theorem assemble (rows : RowFacts) (transport : PacketTransport) : Packets.CompilerLaws := by
  intro sources L target mode q circuit pcpp atoms g r hr
  exact transport (decompositionOf sources) (Packets.request sources L target mode atoms) g r
    (rows sources L target mode atoms r hr)

end PCJc06b3608d6d34481_Plan
