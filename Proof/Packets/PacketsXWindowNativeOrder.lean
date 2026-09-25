import Proof.Packets.PacketsXWindowHomogeneousOrder
import Proof.Packets.PacketsXSingletonSubstitution

/-! The runtime antidiagonal reads j=0,...,d, with elementary degree d-j.
A single reflected singleton cache substitution preserves this exact raw
source order, after which the physical normalizer yields the frozen window. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowNativeOrder
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowBinomial
open NearCubicWires.RepairOrdinary.RowTupleSubsets
open WindowHomogeneousOrder

def positionalShifted (v M offset d : Nat) : Ring.Poly Nat :=
  (List.range (d+1)).flatMap (fun j=>
    gf2ParityScale ((offset+j-1).choose j) (selected v M (d-j)))
def positionalWindow (v M offset width target : Nat) : Ring.Poly Nat :=
  (List.range (width+1)).flatMap (fun d=>
    gf2ParityScale (d.choose target) (positionalShifted v M offset d))

theorem range_desc (d : Nat) : (List.range (d+1)).map (fun j=>d-j)=(List.range (d+1)).reverse := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,List.getElem_reverse,List.length_range]
    omega

theorem nativeShifted_desc (codes : List Nat) (v offset d : Nat) :
    nativeShifted codes v offset d=(List.range (d+1)).flatMap (fun j=>
      gf2ParityScale ((offset+j-1).choose j) (SubsetOrder.reflectedSource v (d-j) codes)) := by
  unfold nativeShifted
  rw [←range_desc,List.flatMap_map]
  apply List.flatMap_congr
  intro j hj
  have hjd : j≤d := by have := List.mem_range.mp hj;omega
  simp only [Nat.sub_sub_self hjd]

theorem map_scale (f : Nat→Nat) (n : Nat) (P : Ring.Poly Nat) :
    (gf2ParityScale n P).map (List.map f)=gf2ParityScale n (P.map (List.map f)) := by
  unfold gf2ParityScale
  split <;> rfl

theorem reflected_shifted (codes : List Nat) (v offset d : Nat) :
    (positionalShifted v codes.length offset d).map (List.map (SubsetOrder.lookup codes.reverse))=
      nativeShifted codes v offset d := by
  rw [nativeShifted_desc]
  unfold positionalShifted
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  rw [map_scale]
  rfl

theorem reflected_window (codes : List Nat) (v offset width target : Nat) :
    (positionalWindow v codes.length offset width target).map (List.map (SubsetOrder.lookup codes.reverse))=
      nativeWindow codes v offset width target := by
  unfold positionalWindow nativeWindow
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro d _
  rw [map_scale,reflected_shifted]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowNativeOrder
