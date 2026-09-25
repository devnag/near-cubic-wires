import Proof.Assembly.Values
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.MatrixScoreBatch
open PCJ9eff70d512234a4c_Fixed
open scoped BigOperators
namespace PCJ843c22a3684945e9_Plan
noncomputable section

def rowSum {q L : Nat} (F : Packets.Family q L)
    (r : Packets.Row F.occurrences L) : Nat :=
  ∑ z : BitInput (Packets.live F)ᶜ.card,
    if r.select z then
      ∑ y : BitInput (Packets.live F).card,
        (evaluateStructuralGF2
          (LiveRows.residualAssignment F.occurrences (Packets.live F)
            (C10SupplierRowInput.joinInput (Packets.live F) y z)) r.reference).toNat
    else 0

def familySum {q L : Nat} (F : Packets.Family q L) : Nat :=
  (F.rows.map (rowSum F)).sum

def RowCertificate : Prop :=
  ∀ {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) (layout : Packets.Layout a F g)
    (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows)
    (facts : Packets.PacketFacts a F g r),
    let d := Packets.datum a F g layout r hr facts
    (∀ i j, d.f i j < 2^d.Q) ∧
    (∀ i j, Int.ModEq ((2 : Int)^d.Q)
      (SupplierPrinter.weightedDominance (leftScore (EquationRow.request d.row))
        (rightScore (EquationRow.request d.row)) (weight (EquationRow.request d.row)) i j)
      (d.f i j)) ∧
    PCJ9eff70d512234a4c_Fixed.datumValue d = rowSum F r

def RequestSum : Prop :=
  ∀ (sources : EightSources) (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)),
    familySum (Packets.request sources L target mode atoms) =
      (LiveRows.fraction sources L target mode atoms).1

theorem parent (rows : RowCertificate) (family : RequestSum) : TableCertificate := by
  intro sources L target mode q circuit pcpp atoms g layout facts
  let F := Packets.request sources L target mode atoms
  let a := decompositionOf sources
  constructor
  · intro d hd
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hd
    have h := rows a F g layout r.val r.property (facts r.val r.property)
    exact ⟨h.1, fun i => h.2.1 i.divNat i.modNat⟩
  · change ((dataList a F g layout facts).map PCJ9eff70d512234a4c_Fixed.datumValue).sum = _
    calc
      _ = (F.rows.attach.map (fun r => rowSum F r.val)).sum := by
        apply congrArg List.sum
        simp only [dataList, List.map_map]
        apply List.map_congr_left
        intro r _
        exact (rows a F g layout r.val r.property (facts r.val r.property)).2.2
      _ = familySum F := by simp [familySum]
      _ = _ := family sources L target mode atoms
end
end PCJ843c22a3684945e9_Plan
