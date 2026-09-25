import Proof.Packets.PacketsXSubstitutionScanTyped
import Proof.Packets.SubstitutionOuterData

/-! Exact product meaning in the original natural literal codes. Finite mask
coordinates are only bounded representations, not a change of variable codes. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.CanonicalFourfoldRowProgram
open PhysicalPacketMasks NormalizedFiniteTransport

theorem one_mask (C : Nat) : (([[]] : Ring.Poly (Fin C)).map mask)=SubstitutionOuter.one C := by
  simp [SubstitutionOuter.one,mask]

theorem monomial_nat (C : Nat) (pre post : List Bool) (m : List Nat)
    (hm : m.Pairwise (·<·)) (hc : ∀ j∈m,j<C)
    (atoms : List (Ring.Poly Nat)) (hAtoms : ∀ P∈atoms,Fits C P) (left : Packet) :
    (scan C pre.length (pre++maskNat C m++post) (atoms.map (List.map (maskNat C)))
      left (SubstitutionOuter.one C) C).2=
      (NormalizedFolds.product (m.map (fun j=>atoms.getD j []))).map (maskNat C) := by
  let typed:=atoms.map (lift C)
  have encodeAtoms : typed.map (List.map mask)=atoms.map (List.map (maskNat C)) := by
    unfold typed
    rw [List.map_map]
    apply List.map_congr_left
    intro P hp
    exact masks_lift C P (hAtoms P hp)
  have downAtoms : typed.map down=atoms := by
    unfold typed
    rw [List.map_map]
    calc
      _=atoms.map id := List.map_congr_left (fun P hp=>lift_down C P (hAtoms P hp))
      _=atoms := List.map_id _
  have selected (j : Nat) : down (typed.getD j [])=atoms.getD j [] := by
    have h:=List.getD_map typed [] (down (C:=C)) (n:=j)
    rw [downAtoms] at h
    exact h.symm
  have h:=monomial_product C pre post m hm hc typed left
  rw [encodeAtoms,one_mask C,masks_down,product_down] at h
  have hmapped : (m.map (fun j=>typed.getD j [])).map down=m.map (fun j=>atoms.getD j []) := by
    simp only [List.map_map,Function.comp_def,selected]
  rw [hmapped] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
