import Mathlib.Data.Fintype.Fin
import Proof.Packets.MajorityCount
import Proof.Packets.PacketsXPairedPacketMeaning
import Proof.Packets.UnaryCompareFlag

/-! Exact finite-code meaning of the physically counted majority predicate
and of the bit-selected product, including the even and empty cases. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityPredicateMeaning
open NearCubicWires NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalk
open NearCubicWires.CanonicalFourfoldRowProgram
open Theorem25Completion PairedPacketMeaning

theorem marks_ofFn {n : Nat} (bits : Fin n→Bool) :
    (CycleCellBitCount.marks (List.ofFn bits)).length=
      ((Finset.univ : Finset (Fin n)).filter fun i=>bits i=true).card := by
  induction n with
  | zero=>simp [CycleCellBitCount.marks]
  | succ n ih=>
    rw [List.ofFn_succ,Fin.card_filter_univ_succ]
    have h:=ih (fun i=>bits i.succ)
    cases hb : bits 0 <;>simpa [CycleCellBitCount.marks,hb,Nat.add_comm] using h

theorem predicate {n : Nat} (bits : Fin n→Bool) :
    decide ((n+1)/2≤(CycleCellBitCount.marks (List.ofFn bits)).length)=compiledBitMajority bits := by
  rw [marks_ofFn]
  rfl

theorem factors_ofFn {n : Nat} (ps : Fin n→Poly) (bits : Fin n→Bool) :
    factors (List.ofFn ps) (List.ofFn bits)=
      List.ofFn (fun i=>if bits i then ps i else Ring.add [[]] (ps i)) := by
  apply List.ext_getElem
  · simp [factors]
  · intro i h1 h2
    simp [factors,literal]

theorem selector {n : Nat} (ps : Fin n→Poly) (bits : Fin n→Bool) :
    Normalized.structuralGF2Product (factors (List.ofFn ps) (List.ofFn bits))=
      Normalized.structuralGF2BooleanSelector ps bits := by
  rw [factors_ofFn]
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityPredicateMeaning
