import Proof.CaseAnalysis.RowsModeLiteralPair

/-! Exact raw-list meanings of the physically emitted literal pairs.
The two members use the same occurrence index, including masked constants. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralMeaning
open CanonicalFourfoldRowProgram SupplierToeplitzCore SupplierToeplitz CloseoutRowsModeLiteralPair
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def polynomial (neg bit : Bool) (index : Nat):=
  (pair neg bit index).1++(pair neg bit index).2

theorem positive {population : Nat} (mask : Finset (Fin population)) (coordinate : Fin population) (selected : Bool) :
    polynomial false (selected&&decide (coordinate∈mask)) coordinate.val=
      if selected then structuralMaskedCoordinate mask coordinate else structuralGF2Zero:=by
  cases selected <;> by_cases hm:coordinate∈mask <;>
    simp [polynomial,pair,structuralMaskedCoordinate,structuralGF2Variable,structuralGF2Zero,hm]

theorem negative {population : Nat} (mask : Finset (Fin population)) (coordinate : Fin population) (selected : Bool) :
    polynomial selected (selected&&decide (coordinate∈mask)) coordinate.val=
      if selected then structuralGF2Not (structuralMaskedCoordinate mask coordinate) else structuralGF2Zero:=by
  cases selected <;> by_cases hm:coordinate∈mask <;>
    simp [polynomial,pair,structuralMaskedCoordinate,structuralGF2Variable,structuralGF2Zero,
      structuralGF2Not,structuralGF2Add,structuralGF2One,hm]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralMeaning
