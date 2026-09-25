import Proof.Packets.PacketsXNormalizerOperations

/-! The restored physical literal cache emits raw constant/variable pairs.
Their actual ordered normalization is exactly the frozen normalized atom,
including the order of the two monomials of a negative selected literal. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralAtomNormalize
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierToeplitzCore

theorem masked_eq {population : Nat} (mask : Finset (Fin population)) (i : Fin population) :
    Normalized.structuralMaskedCoordinate mask i=Ring.norm (structuralMaskedCoordinate mask i) := by
  by_cases hm:i∈mask
  · simp only [Normalized.structuralMaskedCoordinate,structuralMaskedCoordinate,if_pos hm]
    rfl
  · simp only [Normalized.structuralMaskedCoordinate,structuralMaskedCoordinate,if_neg hm]
    rfl

theorem not_masked_eq {population : Nat} (mask : Finset (Fin population)) (i : Fin population) :
    Normalized.structuralGF2Not (Normalized.structuralMaskedCoordinate mask i)=
      Ring.norm (structuralGF2Not (structuralMaskedCoordinate mask i)) := by
  by_cases hm:i∈mask
  · simp only [Normalized.structuralMaskedCoordinate,structuralMaskedCoordinate,if_pos hm]
    rfl
  · simp only [Normalized.structuralMaskedCoordinate,structuralMaskedCoordinate,if_neg hm]
    rfl

theorem atom_eq {rank depth population : Nat}
    (mask : Finset (Fin population)) (label : Fin population→BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : Nat) :
    Normalized.structuralListLiteralAtom (depth:=depth) mask label seed code=
      Ring.norm (structuralListLiteralAtom (depth:=depth) mask label seed code) := by
  unfold Normalized.structuralListLiteralAtom structuralListLiteralAtom
  cases hd:decodeListLiteralVariable depth population code with
  | none=>rfl
  | some literal=>
    cases literal with
    | terminal coordinate=>
      dsimp only
      split
      · exact masked_eq mask coordinate
      · rfl
    | delta level slot=>
      dsimp only
      cases hs:decodeListLiteralSlot slot with
      | inl coordinate=>
        dsimp only
        split
        · exact masked_eq mask coordinate
        · rfl
      | inr coordinate=>
        dsimp only
        split
        · exact not_masked_eq mask coordinate
        · rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralAtomNormalize
