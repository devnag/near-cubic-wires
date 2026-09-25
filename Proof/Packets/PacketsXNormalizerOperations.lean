import Proof.Packets.PacketsXNormalizerEncoding

/-! Exact ordered raw inputs for each normalized arithmetic primitive. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
open PhysicalCoefficientAlgebra
variable {α : Type}

 theorem ordered_of_nodup [DecidableEq α] (P : List α) (hn : P.Nodup) : ordered P=P.reverse := by
  induction P using List.reverseRecOn with
  | nil => rfl
  | append_singleton P x ih =>
    have hP : P.Nodup := hn.of_append_left
    have hx : x∉P := by
      intro hx
      exact (List.nodup_append.mp hn).2.2 x hx x (by simp) rfl
    have hx' : x∉ordered P := by
      rw [ih hP]
      simpa only [List.mem_reverse] using hx
    rw [ordered_snoc,toggle,if_neg hx',ih hP]
    simp only [List.reverse_append,List.reverse_singleton,List.singleton_append]

 theorem ring_toggle [DecidableEq α] (m : List α) (P : Ring.Poly α) :
    toggle m P=Ring.toggle m P := by
  unfold toggle Ring.toggle
  split
  · simp only [List.erase_eq_eraseP,beq_eq_decide]
  · rfl

 theorem norm_ordered [LinearOrder α] (P : Ring.Poly α) :
    Ring.norm P=ordered (P.map Ring.canon) := by
  rw [ordered_eq_fold,List.foldl_map]
  unfold Ring.norm
  apply congrArg (fun f=>List.foldl f [] P)
  funext acc m
  exact (ring_toggle (Ring.canon m) acc).symm

 theorem canon_eq_of_pairwise [LinearOrder α] (m : List α) (hm : m.Pairwise (·<·)) : Ring.canon m=m := by
  apply Ring.pairwise_toFinset_injective (Ring.canon_pairwise m) hm
  ext x
  simp only [List.mem_toFinset,Ring.canon_mem]

 theorem norm_normal [LinearOrder α] (P : Ring.Poly α) (hP : Ring.Normal P) : Ring.norm P=P.reverse := by
  rw [norm_ordered]
  have he : P.map Ring.canon=P := by
    calc
      P.map Ring.canon=P.map id := List.map_congr_left (fun m hm=>canon_eq_of_pairwise m (hP.2 m hm))
      _=P := List.map_id P
  rw [he]
  exact ordered_of_nodup P hP.1

 theorem norm_reverse_normal [LinearOrder α] (P : Ring.Poly α) (hP : Ring.Normal P) : Ring.norm P.reverse=P := by
  have hr : Ring.Normal P.reverse := ⟨List.nodup_reverse.mpr hP.1,
    fun m hm=>hP.2 m (List.mem_reverse.mp hm)⟩
  rw [norm_normal P.reverse hr,List.reverse_reverse]

 theorem fold_canon_eq [LinearOrder α] (Q A : Ring.Poly α)
    (hQ : ∀ m∈Q,m.Pairwise (·<·)) :
    Q.foldl (fun acc m=>Ring.toggle (Ring.canon m) acc) A=
      Q.foldl (fun acc m=>Ring.toggle m acc) A := by
  induction Q generalizing A with
  | nil => rfl
  | cons m Q ih =>
    simp only [List.foldl_cons,canon_eq_of_pairwise m (hQ m (by simp))]
    exact ih _ (fun n hn=>hQ n (by simp [hn]))

/-- Reverse the normalized left operand before concatenating the right one.
The normalizer then reproduces Ring.add's accumulator order exactly. -/
theorem add_raw [LinearOrder α] (P Q : Ring.Poly α)
    (hP : Ring.Normal P) (hQ : Ring.Normal Q) :
    Ring.norm (P.reverse++Q)=Ring.add P Q := by
  unfold Ring.norm
  rw [List.foldl_append]
  change Q.foldl (fun acc m=>Ring.toggle (Ring.canon m) acc) (Ring.norm P.reverse)=_
  rw [norm_reverse_normal P hP,fold_canon_eq Q P hQ.2]
  rfl

/-- Cartesian support unions are normalized in the compiler's literal
left-major, right-minor traversal order. -/
theorem mul_raw [LinearOrder α] (P Q : Ring.Poly α) :
    Ring.norm (P.flatMap (fun m=>Q.map (fun n=>m++n)))=Ring.mul P Q := by
  simp only [Ring.norm,List.foldl_flatMap,List.foldl_map,Ring.mul]

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
