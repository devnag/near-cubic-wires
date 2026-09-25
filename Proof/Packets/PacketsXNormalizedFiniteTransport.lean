import Proof.Packets.PacketsXNormalizerOperations

/-! Exact ordered transport between finite physical coordinates and the
original natural literal codes. Fin.val preserves ordering and all codes;
this is stronger than evaluation or permutation equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedFiniteTransport
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
variable {C : Nat}

def down (P : Ring.Poly (Fin C)) : Ring.Poly Nat := P.map (List.map Fin.val)

theorem monomial_injective : Function.Injective (List.map (Fin.val : Fin C→Nat)) :=
  List.map_injective_iff.mpr Fin.val_injective

theorem canon_down (m : List (Fin C)) : (Ring.canon m).map Fin.val=Ring.canon (m.map Fin.val) := by
  refine Ring.pairwise_toFinset_injective ?_ (Ring.canon_pairwise _) ?_
  · exact List.pairwise_map.mpr (Ring.canon_pairwise m)
  · ext n
    simp only [List.mem_toFinset,List.mem_map,Ring.canon_mem]

theorem norm_down (P : Ring.Poly (Fin C)) : down (Ring.norm P)=Ring.norm (down P) := by
  simp only [down,NormalizerOrder.norm_ordered]
  rw [←NormalizerOrder.ordered_map (List.map Fin.val) monomial_injective]
  apply congrArg NormalizerOrder.ordered
  simp only [List.map_map]
  apply List.map_congr_left
  intro m _
  exact canon_down m

theorem add_down (P Q : Ring.Poly (Fin C)) : down (Ring.add P Q)=Ring.add (down P) (down Q) := by
  have h:=NormalizerOrder.fold_toggle_map (List.map Fin.val) monomial_injective Q P
  simp only [NormalizerOrder.ring_toggle] at h
  exact h

theorem mul_down (P Q : Ring.Poly (Fin C)) : down (Ring.mul P Q)=Ring.mul (down P) (down Q) := by
  rw [←NormalizerOrder.mul_raw, norm_down, ←NormalizerOrder.mul_raw]
  apply congrArg Ring.norm
  simp only [down,List.map_flatMap,List.map_map,List.flatMap_map]
  apply List.flatMap_congr
  intro m _
  apply List.map_congr_left
  intro n _
  exact List.map_append

def liftMonomial (C : Nat) (m : List Nat) : List (Fin C) :=
  m.filterMap (fun n=>if h:n<C then some ⟨n,h⟩ else none)
def lift (C : Nat) (P : Ring.Poly Nat) : Ring.Poly (Fin C) := P.map (liftMonomial C)
def Fits (C : Nat) (P : Ring.Poly Nat) : Prop := ∀ m∈P,∀ code∈m,code<C

theorem liftMonomial_down (C : Nat) (m : List Nat) (hm : ∀ code∈m,code<C) :
    (liftMonomial C m).map Fin.val=m := by
  induction m with
  | nil=>rfl
  | cons n m ih=>
    have hn:=hm n (by simp)
    have ht:=ih (fun code hc=>hm code (by simp [hc]))
    simpa only [liftMonomial,List.filterMap_cons,dif_pos hn,List.map_cons] using congrArg (List.cons n) ht

theorem lift_down (C : Nat) (P : Ring.Poly Nat) (hP : Fits C P) : down (lift C P)=P := by
  unfold down lift
  rw [List.map_map]
  calc
    _=P.map id := List.map_congr_left (fun m hm=>liftMonomial_down C m (hP m hm))
    _=P := List.map_id P

theorem normal_of_down {P : Ring.Poly (Fin C)} (hP : Ring.Normal (down P)) : Ring.Normal P := by
  refine ⟨List.Nodup.of_map (List.map Fin.val) hP.1,?_⟩
  intro m hm
  have h:=hP.2 (m.map Fin.val) (List.mem_map.mpr ⟨m,hm,rfl⟩)
  rw [List.pairwise_map] at h
  exact h

theorem normal_lift (C : Nat) (P : Ring.Poly Nat) (hP : Fits C P) (hn : Ring.Normal P) :
    Ring.Normal (lift C P) := by
  apply normal_of_down
  rwa [lift_down C P hP]

def maskNat (C : Nat) (m : List Nat) : List Bool := List.ofFn (fun i : Fin C=>decide (i.val∈m))

theorem mask_down (m : List (Fin C)) : maskNat C (m.map Fin.val)=PhysicalPacketMasks.mask m := by
  unfold maskNat PhysicalPacketMasks.mask
  apply congrArg List.ofFn
  funext i
  simp only [List.mem_map_of_injective Fin.val_injective]

theorem masks_lift (C : Nat) (P : Ring.Poly Nat) (hP : Fits C P) :
    (lift C P).map PhysicalPacketMasks.mask=P.map (maskNat C) := by
  unfold lift
  rw [List.map_map]
  apply List.map_congr_left
  intro m hm
  dsimp only [Function.comp_def]
  rw [←mask_down,liftMonomial_down C m (hP m hm)]

theorem masks_down (P : Ring.Poly (Fin C)) :
    P.map PhysicalPacketMasks.mask=(down P).map (maskNat C) := by
  simp only [down,List.map_map]
  apply List.map_congr_left
  intro m _
  exact (mask_down m).symm

theorem normalized_masks_nat (C : Nat) (P : Ring.Poly Nat) (hP : Fits C P) :
    NormalizerOrder.ordered (P.map (maskNat C))=(Ring.norm P).map (maskNat C) := by
  have h:=NormalizerOrder.normalized_masks (lift C P)
  rw [masks_lift C P hP,masks_down,norm_down,lift_down C P hP] at h
  exact h


end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedFiniteTransport
