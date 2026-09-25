import Proof.Assembly.FixedCore
import Proof.CaseAnalysis.FinalPrinterMonomials

/-! Boolean squarefree normalization used by the fixed packet compiler.
All evaluation statements hold on every Boolean assignment. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option linter.unusedVariables false

open NearCubicWires.SupplierPrinter
open scoped BigOperators
namespace PCJ9eff70d512234a4c_Fixed.Ring

variable {α : Type}

@[simp] theorem canon_mem [LinearOrder α] {m : List α} {x : α} :
    x ∈ canon m ↔ x ∈ m := by
  simp [canon]

theorem canon_length_le [LinearOrder α] (m : List α) :
    (canon m).length ≤ m.length := by
  exact (List.dedup_sublist _).length_le.trans_eq (List.length_insertionSort _ _)

theorem canon_pairwise [LinearOrder α] (m : List α) : (canon m).Pairwise (· < ·) := by
  have hn : (canon m).Nodup := List.nodup_dedup _
  have hs : (canon m).Pairwise (· ≤ ·) :=
    (List.pairwise_insertionSort (· ≤ ·) m).sublist (List.dedup_sublist _)
  exact (hs.and hn).imp (fun h => lt_of_le_of_ne h.1 h.2)

theorem mem_toggle [DecidableEq α] {m n : List α} {P : Poly α}
    (h : n ∈ toggle m P) : n = m ∨ n ∈ P := by
  unfold toggle at h
  split at h
  · exact Or.inr (List.mem_of_mem_erase h)
  · simpa only [List.mem_cons] using h

theorem fold_toggle_property [DecidableEq α] (T : List α → Prop)
    (f : List α → List α) (Q P : Poly α)
    (hP : ∀ m ∈ P, T m) (hQ : ∀ m ∈ Q, T (f m)) :
    ∀ m ∈ Q.foldl (fun acc n => toggle (f n) acc) P, T m := by
  induction Q generalizing P with
  | nil => exact hP
  | cons n Q ih =>
    apply ih
    · intro m hm
      rcases mem_toggle hm with rfl | hm
      · exact hQ n (by simp)
      · exact hP m hm
    · intro m hm
      exact hQ m (by simp [hm])

theorem degree_norm [LinearOrder α] {d : Nat} {P : Poly α} (hP : Degree d P) :
    Degree d (norm P) := by
  apply fold_toggle_property (fun m => m.length ≤ d) canon P []
  · simp
  · intro m hm
    exact (canon_length_le m).trans (hP m hm)

theorem degree_add [DecidableEq α] {d e : Nat} {P Q : Poly α}
    (hP : Degree d P) (hQ : Degree e Q) : Degree (max d e) (add P Q) := by
  apply fold_toggle_property (fun m => m.length ≤ max d e) id Q P
  · intro m hm
    exact (hP m hm).trans (Nat.le_max_left _ _)
  · intro m hm
    exact (hQ m hm).trans (Nat.le_max_right _ _)

theorem degree_mul [LinearOrder α] {d e : Nat} {P Q : Poly α}
    (hP : Degree d P) (hQ : Degree e Q) : Degree (d + e) (mul P Q) := by
  unfold mul
  have aux (A : Poly α) (hA : Degree (d + e) A) :
      Degree (d + e) (P.foldl (fun acc m =>
        Q.foldl (fun acc n => toggle (canon (m ++ n)) acc) acc) A) := by
    induction P generalizing A with
    | nil => exact hA
    | cons m P ih =>
      apply ih
      · intro n hn
        exact hP n (by simp [hn])
      · apply fold_toggle_property (fun n => n.length ≤ d + e)
          (fun n => canon (m ++ n)) Q A hA
        intro n hn
        exact (canon_length_le _).trans (by
          rw [List.length_append]
          exact Nat.add_le_add (hP m (by simp)) (hQ n hn))
  exact aux [] (by simp [Degree])

theorem normal_toggle [LinearOrder α] {m : List α} {P : Poly α}
    (hm : m.Pairwise (· < ·)) (hP : Normal P) : Normal (toggle m P) := by
  unfold toggle
  split
  · refine ⟨hP.1.erase _, fun n hn => hP.2 n (List.mem_of_mem_erase hn)⟩
  · refine ⟨List.nodup_cons.mpr ⟨by assumption, hP.1⟩, ?_⟩
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hm
    · exact hP.2 n hn

theorem normal_fold [LinearOrder α] (f : List α → List α) (P Q : Poly α)
    (hP : Normal P) (hQ : ∀ m ∈ Q, (f m).Pairwise (· < ·)) :
    Normal (Q.foldl (fun acc m => toggle (f m) acc) P) := by
  induction Q generalizing P with
  | nil => exact hP
  | cons m Q ih =>
    apply ih _ (normal_toggle (hQ m (by simp)) hP)
    intro n hn
    exact hQ n (by simp [hn])

theorem normal_norm [LinearOrder α] (P : Poly α) : Normal (norm P) := by
  apply normal_fold canon [] P
  · simp [Normal]
  · intro m hm
    exact canon_pairwise m

theorem normal_add [LinearOrder α] {P Q : Poly α}
    (hP : Normal P) (hQ : Normal Q) : Normal (add P Q) :=
  normal_fold id P Q hP hQ.2

theorem normal_mul [LinearOrder α] (P Q : Poly α) : Normal (mul P Q) := by
  unfold mul
  have aux (A : Poly α) (hA : Normal A) :
      Normal (P.foldl (fun acc m =>
        Q.foldl (fun acc n => toggle (canon (m ++ n)) acc) acc) A) := by
    induction P generalizing A with
    | nil => exact hA
    | cons m P ih =>
      apply ih
      exact normal_fold (fun n => canon (m ++ n)) A Q hA
        (fun n _ => canon_pairwise _)
  exact aux [] (by simp [Normal])

theorem support_norm [LinearOrder α] (S : Finset α) (P : Poly α)
    (hP : ∀ m ∈ P, ∀ x ∈ m, x ∈ S) :
    ∀ m ∈ norm P, ∀ x ∈ m, x ∈ S := by
  apply fold_toggle_property (fun m => ∀ x ∈ m, x ∈ S) canon P []
  · simp
  · intro m hm x hx
    exact hP m hm x (canon_mem.mp hx)

theorem pairwise_toFinset_injective [LinearOrder α] {m n : List α}
    (hm : m.Pairwise (· < ·)) (hn : n.Pairwise (· < ·))
    (h : m.toFinset = n.toFinset) : m = n := by
  have hp : m.Perm n := (List.perm_ext_iff_of_nodup hm.nodup hn.nodup).mpr (by
    intro x
    exact Iff.trans List.mem_toFinset.symm (h ▸ List.mem_toFinset))
  exact hp.eq_of_pairwise' hm hn

/-- A normal polynomial's monomials inject into the subsets of its actual local
alphabet. No live-assignment multiplicity appears in this bound. -/
theorem size_bound [LinearOrder α] {P : Poly α} (S : Finset α) (d : Nat)
    (hP : Normal P) (hd : Degree d P)
    (hS : ∀ m ∈ P, ∀ x ∈ m, x ∈ S) : P.length ≤ (S.card + 1)^d := by
  classical
  let supports := P.toFinset.image List.toFinset
  have hinj : Set.InjOn (fun m : List α => m.toFinset) (↑P.toFinset : Set (List α)) := by
    intro m hm n hn h
    exact pairwise_toFinset_injective (hP.2 m (List.mem_toFinset.mp hm))
      (hP.2 n (List.mem_toFinset.mp hn)) h
  have hcard : supports.card = P.length := by
    rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hP.1]
  have hsub : supports ⊆ (Finset.range (d+1)).biUnion (fun j => S.powersetCard j) := by
    intro support hs
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hs
    have hm' : m ∈ P := List.mem_toFinset.mp hm
    apply Finset.mem_biUnion.mpr
    refine ⟨m.toFinset.card, Finset.mem_range.mpr (by
      have hle := (List.toFinset_card_le m).trans (hd m hm')
      omega), Finset.mem_powersetCard.mpr ⟨?_, rfl⟩⟩
    intro x hx
    exact hS m hm' x (List.mem_toFinset.mp hx)
  calc
    P.length = supports.card := hcard.symm
    _ ≤ ((Finset.range (d+1)).biUnion (fun j => S.powersetCard j)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (d+1), (S.powersetCard j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (d+1), S.card.choose j := by simp only [Finset.card_powersetCard]
    _ ≤ (S.card+1)^d :=
      NearCubicWires.RepairSource.CloseoutFinal.C10PrinterMonomials.sum_choose_le_succ_pow _ _

end PCJ9eff70d512234a4c_Fixed.Ring
