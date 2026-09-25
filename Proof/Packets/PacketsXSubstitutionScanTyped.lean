import Proof.Packets.SubstitutionScan
import Proof.Packets.PacketsXNormalizedMultiplyTyped
import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXNormalizedFolds
import Mathlib.Data.List.GetD

/-! Exact literal-code meaning of the backward mask scan. The physical scan
uses the ascending natural code positions and therefore realizes the frozen
right-fold product of the original sorted monomial, with no renumbering. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.CanonicalFourfoldRowProgram
open PhysicalPacketMasks NormalizedFiniteTransport

variable {B : Nat}

theorem mul_masks (P Q : Ring.Poly (Fin B)) :
    NormalizerOrder.ordered (MaskProduct.unions (P.map mask) (Q.map mask))=
      (Ring.mul P Q).map mask := by
  rw [NormalizedMultiply.unions_masks,NormalizerOrder.normalized_masks,NormalizerOrder.mul_raw]

theorem codes_fold_masks (codes : List Nat) (bits : Nat→Bool)
    (atoms : List (Ring.Poly (Fin B))) (initial : Ring.Poly (Fin B)) :
    codes.foldr (fun j acc=>if bits j then
      NormalizerOrder.ordered (MaskProduct.unions ((atoms.map (List.map mask)).getD j []) acc)
      else acc) (initial.map mask)=
    (codes.foldr (fun j acc=>if bits j then Ring.mul (atoms.getD j []) acc else acc) initial).map mask := by
  induction codes with
  | nil=>rfl
  | cons j codes ih=>
    simp only [List.foldr_cons]
    rw [ih]
    cases bits j
    · rfl
    · simp only [↓reduceIte]
      have hg : (atoms.map (List.map mask)).getD j []=(atoms.getD j []).map mask :=
        List.getD_map atoms [] (List.map mask)
      rw [hg,mul_masks]

theorem scan_typed (C base : Nat) (source : List Bool) (atoms : List (Ring.Poly (Fin B)))
    (left : Packet) (initial : Ring.Poly (Fin B)) :
    (scan C base source (atoms.map (List.map mask)) left (initial.map mask) C).2=
      ((List.range' 0 C).foldr (fun j acc=>if readTapeBit source (base+j) then
        Ring.mul (atoms.getD j []) acc else acc) initial).map mask := by
  rw [scan_complete]
  exact codes_fold_masks _ _ _ _

theorem read_mask (C : Nat) (pre post : List Bool) (m : List Nat) (j : Nat) (hj : j<C) :
    readTapeBit (pre++maskNat C m++post) (pre.length+j)=decide (j∈m) := by
  unfold readTapeBit
  rw [List.append_assoc,List.getD_append_right _ _ _ _ (by omega),Nat.add_sub_cancel_left]
  have hm : (maskNat C m).length=C := List.length_ofFn
  rw [List.getD_append _ _ _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_ofFn _

theorem selected_codes (C : Nat) (m : List Nat) (hm : m.Pairwise (·<·))
    (hc : ∀ j∈m,j<C) : (List.range C).filter (fun j=>decide (j∈m))=m := by
  apply Ring.pairwise_toFinset_injective (List.pairwise_lt_range.filter _) hm
  ext j
  simp only [List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
  exact ⟨fun h=>h.2,fun h=>⟨hc j h,h⟩⟩

theorem mask_fold (C : Nat) (pre post : List Bool) (m : List Nat)
    (hm : m.Pairwise (·<·)) (hc : ∀ j∈m,j<C)
    (atoms : List (Ring.Poly (Fin B))) (initial : Ring.Poly (Fin B)) :
    (List.range' 0 C).foldr (fun j acc=>
      if readTapeBit (pre++maskNat C m++post) (pre.length+j) then
        Ring.mul (atoms.getD j []) acc else acc) initial=
      m.foldr (fun j acc=>Ring.mul (atoms.getD j []) acc) initial := by
  rw [←List.range_eq_range']
  have eqOn (js : List Nat) (hj : ∀ j∈js,j<C) :
      js.foldr (fun j acc=>if readTapeBit (pre++maskNat C m++post) (pre.length+j) then
        Ring.mul (atoms.getD j []) acc else acc) initial=
      js.foldr (fun j acc=>if decide (j∈m) then Ring.mul (atoms.getD j []) acc else acc) initial := by
    induction js with
    | nil=>rfl
    | cons j js ih=>
      simp only [List.foldr_cons,read_mask C pre post m j (hj j (by simp))]
      rw [ih (fun x hx=>hj x (by simp [hx]))]
  rw [eqOn _ (fun j hj=>List.mem_range.mp hj),←List.foldr_filter,selected_codes C m hm hc]

theorem monomial_product (C : Nat) (pre post : List Bool) (m : List Nat)
    (hm : m.Pairwise (·<·)) (hc : ∀ j∈m,j<C)
    (atoms : List (Ring.Poly (Fin B))) (left : Packet) :
    (scan C pre.length (pre++maskNat C m++post) (atoms.map (List.map mask))
      left (([[]] : Ring.Poly (Fin B)).map mask) C).2=
      ((m.map (fun j=>atoms.getD j [])).foldr Ring.mul [[]]).map mask := by
  rw [scan_typed,mask_fold C pre post m hm hc,List.foldr_map]

/-- Mapping finite output supports back to their unchanged natural codes
commutes with every multiplication in the frozen product. -/
theorem product_down (polynomials : List (Ring.Poly (Fin B))) :
    down (polynomials.foldr Ring.mul [[]])=
      NormalizedFolds.product (polynomials.map down) := by
  rw [NormalizedFolds.product_exact]
  change down (polynomials.foldr Ring.mul [[]])=(polynomials.map down).foldr Ring.mul [[]]
  induction polynomials with
  | nil=>rfl
  | cons P ps ih=>simp only [List.foldr_cons,List.map_cons,mul_down,ih]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
