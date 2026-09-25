import Proof.Packets.PacketsXSubstitutionScanNat

/-! Exact natural-code value at every inner-loop boundary. This is the product
of precisely the set bits already read by the actual backward source scan. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.CanonicalFourfoldRowProgram
open PhysicalPacketMasks NormalizedFiniteTransport

def selected (C base : Nat) (source : List Bool) (k : Nat) : List Nat :=
  (List.range' (C-k) k).filter (fun j=>readTapeBit source (base+j))

theorem prefix_typed {B : Nat} (C base : Nat) (source : List Bool)
    (atoms : List (Ring.Poly (Fin B))) (left : Packet) (k : Nat) (hk : k≤C) :
    (scan C base source (atoms.map (List.map mask)) left (([[]] : Ring.Poly (Fin B)).map mask) k).2=
      (((selected C base source k).map (fun j=>atoms.getD j [])).foldr Ring.mul [[]]).map mask := by
  rw [scan_snd_eq_foldr C base source _ left _ k hk,codes_fold_masks]
  rw [←List.foldr_filter]
  simp only [selected,List.foldr_map]

theorem prefix_nat (C base : Nat) (source : List Bool)
    (atoms : List (Ring.Poly Nat)) (hAtoms : ∀ P∈atoms,Fits C P) (left : Packet) (k : Nat) (hk : k≤C) :
    (scan C base source (atoms.map (List.map (maskNat C))) left (SubstitutionOuter.one C) k).2=
      (NormalizedFolds.product ((selected C base source k).map (fun j=>atoms.getD j []))).map (maskNat C) := by
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
  have get (j : Nat) : down (typed.getD j [])=atoms.getD j [] := by
    have h:=List.getD_map typed [] (down (C:=C)) (n:=j)
    rw [downAtoms] at h
    exact h.symm
  have h:=prefix_typed C base source typed left k hk
  rw [encodeAtoms,one_mask C,masks_down,product_down] at h
  have hmapped : ((selected C base source k).map (fun j=>typed.getD j [])).map down=
      (selected C base source k).map (fun j=>atoms.getD j []) := by
    simp only [List.map_map,Function.comp_def,get]
  rw [hmapped] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
