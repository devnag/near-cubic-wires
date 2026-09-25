import Proof.Packets.Normalizer

/-! The exact batch order consumed by normalized addition. Reversing the
already-normal accumulator is necessary because the toggle fold prepends. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true

namespace PCJ6ffe03e3512f426d.Normalizer
open PCJ9eff70d512234a4c_Fixed

theorem fold_toggle_disjoint {α : Type} [LinearOrder α] :
    ∀ (P A : Ring.Poly α), P.Nodup → (∀ m ∈ P, m ∉ A) →
      P.foldl (fun acc m => Ring.toggle m acc) A = P.reverse ++ A
  | [], A, _, _ => by simp
  | m::P, A, hn, hd => by
      have hm : m ∉ A := hd m (by simp)
      have hp := List.nodup_cons.mp hn
      have hdis : ∀ n ∈ P, n ∉ m::A := by
        intro n hnp hmem
        rcases List.mem_cons.mp hmem with he | he
        · subst n
          exact hp.1 hnp
        · exact hd n (List.mem_cons_of_mem _ hnp) he
      rw [List.foldl_cons]
      have ht : Ring.toggle m A=m::A := by simp [Ring.toggle,hm]
      rw [ht,fold_toggle_disjoint P (m::A) hp.2 hdis]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem fold_canon_of_fixed {α : Type} [LinearOrder α] :
    ∀ (P A : Ring.Poly α), (∀ m ∈ P, Ring.canon m=m) →
      P.foldl (fun acc m => Ring.toggle (Ring.canon m) acc) A =
        P.foldl (fun acc m => Ring.toggle m acc) A
  | [], _, _ => rfl
  | m::P, A, h => by
      rw [List.foldl_cons,List.foldl_cons,h m (by simp)]
      exact fold_canon_of_fixed P _ (fun n hn => h n (List.mem_cons_of_mem _ hn))

theorem norm_fixed_nodup {α : Type} [LinearOrder α] (P : Ring.Poly α)
    (hn : P.Nodup) (hc : ∀ m ∈ P, Ring.canon m=m) :
    Ring.norm P=P.reverse := by
  unfold Ring.norm
  rw [fold_canon_of_fixed P [] hc,fold_toggle_disjoint P [] hn (by simp)]
  exact List.append_nil _

end PCJ6ffe03e3512f426d.Normalizer
