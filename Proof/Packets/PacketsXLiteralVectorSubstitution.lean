import Proof.Packets.PacketsXDenseAtomsAccumulation
import Proof.Packets.PacketsXVectorLiteralSupport
import Proof.Packets.PacketsXNormalizedSubstitutionExt

/-! A physically accumulated delta-atom table agrees exactly with the frozen
whole-coordinate substitution. Width-zero terminal atoms are not required. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralVectorSubstitution
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek (Pair)

theorem coordinate {rank depth population : Nat} (mask : Finset (Fin population))
    (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank)
    (wins : Fin depth→Nat) (candidate : Fin (population+1)) (atoms : List (Ring.Poly Nat))
    (h : ∀level : Fin depth,∀slot : Fin (2*population),
      atoms.getD (Nat.pair (level.val+1) slot.val) []=
        Normalized.structuralListLiteralAtom (depth:=depth) mask label seed (Nat.pair (level.val+1) slot.val)) :
    Normalized.structuralGF2Substitute (fun code=>atoms.getD code [])
      (Normalized.structuralListPolynomialVector label seed wins 0 candidate)=
      Normalized.structuralMaskedListCoordinate mask label seed wins 0 candidate := by
  apply NormalizedSubstitutionExt.on_support
  intro monomial hm code hc
  obtain ⟨level,slot,rfl⟩:=VectorLiteralSupport.coordinate label seed wins candidate monomial hm code hc
  exact h level slot

end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralVectorSubstitution
