import Proof.Packets.NormalizerOrderNormalizedPacketProduction

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed
noncomputable section

theorem canon_eq {α : Type} [LinearOrder α] {m : List α} (hs : m.Pairwise (· < ·)) :
    Ring.canon m = m := by
  rw [Ring.canon, (hs.imp le_of_lt).insertionSort_eq]
  exact List.dedup_eq_self.mpr (hs.imp ne_of_lt)

theorem canon_strict {α : Type} [LinearOrder α] (m : List α) :
    (Ring.canon m).Pairwise (· < ·) := by
  have hle : (Ring.canon m).Pairwise (· ≤ ·) :=
    (List.pairwise_insertionSort (· ≤ ·) m).sublist (List.dedup_sublist _)
  have hn : (Ring.canon m).Nodup := List.nodup_dedup _
  exact (hle.and hn).imp (fun h => lt_of_le_of_ne h.1 (by simpa [eq_comm] using h.2))

theorem mem_canon {α : Type} [LinearOrder α] {m : List α} {c : α} (h : c ∈ Ring.canon m) :
    c ∈ m :=
  (List.perm_insertionSort (· ≤ ·) m).subset (List.mem_dedup.mp h)

theorem toggle_normal {α : Type} [LinearOrder α] (m : List α) (P : Ring.Poly α)
    (hm : m.Pairwise (· < ·)) (hp : Ring.Normal P) : Ring.Normal (Ring.toggle m P) := by
  unfold Ring.toggle
  split_ifs with h
  · exact ⟨hp.1.erase _, fun n hn => hp.2 n (List.mem_of_mem_erase hn)⟩
  · refine ⟨List.nodup_cons.mpr ⟨h, hp.1⟩, ?_⟩
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hm
    · exact hp.2 n hn

theorem normal_nil {α : Type} [LinearOrder α] : Ring.Normal ([] : Ring.Poly α) :=
  ⟨List.nodup_nil, by simp⟩

theorem normal_mul {α : Type} [LinearOrder α] (P Q : Ring.Poly α) : Ring.Normal (Ring.mul P Q) := by
  unfold Ring.mul
  suffices h : ∀ (P : Ring.Poly α) (acc : Ring.Poly α), Ring.Normal acc →
      Ring.Normal (P.foldl (fun acc m => Q.foldl (fun acc n => Ring.toggle (Ring.canon (m ++ n)) acc) acc) acc) from
    h P [] normal_nil
  intro P
  induction P with
  | nil => intro acc h; exact h
  | cons m P ih =>
    intro acc hacc
    rw [List.foldl_cons]
    apply ih
    suffices hq : ∀ (Q' : Ring.Poly α) (acc : Ring.Poly α), Ring.Normal acc →
        Ring.Normal (Q'.foldl (fun acc n => Ring.toggle (Ring.canon (m ++ n)) acc) acc) from hq Q acc hacc
    intro Q'
    induction Q' with
    | nil => intro acc h; exact h
    | cons n Q' ihq =>
      intro acc h
      rw [List.foldl_cons]
      exact ihq _ (toggle_normal _ _ (canon_strict _) h)

theorem normal_add {α : Type} [LinearOrder α] (P Q : Ring.Poly α) (hp : Ring.Normal P)
    (hq : ∀ m ∈ Q, m.Pairwise (· < ·)) : Ring.Normal (Ring.add P Q) := by
  unfold Ring.add
  induction Q generalizing P with
  | nil => exact hp
  | cons m Q ih =>
    rw [List.foldl_cons]
    exact ih _ (toggle_normal m P (hq m (by simp)) hp) (fun n hn => hq n (List.mem_cons_of_mem _ hn))

theorem normal_product (ps : List StructuralGF2Polynomial) :
    Ring.Normal (Normalized.structuralGF2Product ps) := by
  cases ps with
  | nil =>
    refine ⟨by simp [Normalized.structuralGF2Product, structuralGF2One], ?_⟩
    intro m hm
    simp [Normalized.structuralGF2Product, structuralGF2One] at hm
    subst hm
    exact List.Pairwise.nil
  | cons p ps =>
    simp only [Normalized.structuralGF2Product, List.foldr_cons]
    exact normal_mul _ _

theorem normal_substitute (atom : ℕ → StructuralGF2Polynomial) (P : StructuralGF2Polynomial) :
    Ring.Normal (Normalized.structuralGF2Substitute atom P) := by
  induction P with
  | nil => exact normal_nil
  | cons m P ih =>
    simp only [Normalized.structuralGF2Substitute, Normalized.structuralGF2Add]
    exact normal_add _ _ (normal_product _) (fun n hn => ih.2 n hn)

/-! ## Codes stay below `N` -/

abbrev Valid (N : ℕ) (P : StructuralGF2Polynomial) : Prop := P1Closure.RawRelabelShape.Valid N P

theorem valid_toggle {N : ℕ} {m : List ℕ} {P : StructuralGF2Polynomial}
    (hm : ∀ c ∈ m, c < N) (hp : Valid N P) : Valid N (Ring.toggle m P) := by
  unfold Ring.toggle
  split_ifs
  · intro n hn c hc
    exact hp n (List.mem_of_mem_erase hn) c hc
  · intro n hn c hc
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hm c hc
    · exact hp n hn c hc

theorem valid_norm {N : ℕ} (P : StructuralGF2Polynomial) (hp : Valid N P) :
    Valid N (Ring.norm P) := by
  unfold Ring.norm
  suffices h : ∀ (P acc : StructuralGF2Polynomial), Valid N P → Valid N acc →
      Valid N (P.foldl (fun acc m => Ring.toggle (Ring.canon m) acc) acc) from h P [] hp (by simp [Valid, P1Closure.RawRelabelShape.Valid])
  intro P
  induction P with
  | nil => intro acc _ h; exact h
  | cons m P ih =>
    intro acc hP hacc
    rw [List.foldl_cons]
    exact ih _ (fun n hn => hP n (List.mem_cons_of_mem _ hn))
      (valid_toggle (fun c hc => hP m (by simp) c (mem_canon hc)) hacc)

theorem valid_mul {N : ℕ} (P Q : StructuralGF2Polynomial) (hp : Valid N P) (hq : Valid N Q) :
    Valid N (Ring.mul P Q) := by
  rw [PCJ6ffe03e3512f426d.Normalizer.mul_eq_norm_productBatch]
  apply valid_norm
  intro m hm c hc
  unfold PCJ6ffe03e3512f426d.Normalizer.productBatch at hm
  obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  rcases List.mem_append.mp hc with hc | hc
  · exact hp l hl c hc
  · exact hq r hr c hc

theorem valid_add {N : ℕ} (P Q : StructuralGF2Polynomial) (hp : Valid N P) (hq : Valid N Q) :
    Valid N (Ring.add P Q) := by
  unfold Ring.add
  induction Q generalizing P with
  | nil => exact hp
  | cons m Q ih =>
    rw [List.foldl_cons]
    exact ih _ (valid_toggle (hq m (by simp)) hp) (fun n hn => hq n (List.mem_cons_of_mem _ hn))

theorem valid_product {N : ℕ} (ps : List StructuralGF2Polynomial) (h : ∀ p ∈ ps, Valid N p) :
    Valid N (Normalized.structuralGF2Product ps) := by
  induction ps with
  | nil =>
    intro m hm c hc
    simp [Normalized.structuralGF2Product, structuralGF2One] at hm
    subst hm
    simp at hc
  | cons p ps ih =>
    simp only [Normalized.structuralGF2Product, List.foldr_cons]
    exact valid_mul _ _ (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem valid_substitute {N : ℕ} (atom : ℕ → StructuralGF2Polynomial) (h : ∀ c, Valid N (atom c))
    (P : StructuralGF2Polynomial) : Valid N (Normalized.structuralGF2Substitute atom P) := by
  induction P with
  | nil => simp [Valid, P1Closure.RawRelabelShape.Valid, Normalized.structuralGF2Substitute, structuralGF2Zero]
  | cons m P ih =>
    simp only [Normalized.structuralGF2Substitute, Normalized.structuralGF2Add]
    exact valid_add _ _ (valid_product _ (by
      intro p hp
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hp
      exact h c)) ih

theorem atom_valid {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (c : ℕ) :
    Valid (C10SupplierRowInput.childList a live occ).length
      (CloseoutRowsUniversal.atomOfCode a live occ c) := by
  unfold CloseoutRowsUniversal.atomOfCode
  split
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · exact P1Closure.RawRelabelShape.cache_valid a _ _ m hm d hd
    · exact P1Closure.RawRelabelShape.cache_valid a _ _ m hm d hd
  · simp [Valid, P1Closure.RawRelabelShape.Valid, structuralGF2Zero]

/-! ## The packet word of one row, through the relabel -/

variable {q L : ℕ} (a : DecompositionAlgorithm) (F : Packets.Family q L) (g : Packets.Geometry F)
  (row : Packets.Row F.occurrences L)

/-- The pooled child count `N` of the relabel. -/
abbrev childCount : ℕ := (C10SupplierRowInput.childList a (Packets.live F) F.occurrences).length

theorem lowered_normal : Ring.Normal (Packets.lowered a F row) :=
  normal_substitute _ _

theorem lowered_valid : Valid (childCount a F) (Packets.lowered a F row) :=
  valid_substitute _ (fun c => valid_norm _ (atom_valid a (Packets.live F) F.occurrences c)) _

theorem poolIndex_val (yi : Fin (C10SupplierRowInput.liveList (Packets.live F)).length) (c : ℕ)
    (hc : c < childCount a F) :
    (C10SupplierRowInput.poolIndex a (Packets.live F) F.occurrences (Packets.residual F) g.arity yi c).val =
      childCount a F * yi.val + c + 1 := by
  simp [C10SupplierRowInput.poolIndex, hc]

/-- The relabel map `Packets.one` applies to each code. -/
def relabel (yi : Fin (C10SupplierRowInput.liveList (Packets.live F)).length) (c : ℕ) :
    Fin (Packets.pool a F g).length :=
  Fin.cast (P1Closure.BinaryPool.pool_length a (Packets.live F) F.occurrences (Packets.residual F) g.arity).symm
    (C10SupplierRowInput.poolIndex a (Packets.live F) F.occurrences (Packets.residual F) g.arity yi c)

theorem relabel_val (yi : Fin (C10SupplierRowInput.liveList (Packets.live F)).length) (c : ℕ)
    (hc : c < childCount a F) : (relabel a F g yi c).val = childCount a F * yi.val + c + 1 := by
  simp only [relabel, Fin.val_cast]
  exact poolIndex_val a F g yi c hc

/-- **One packet is the reversed relabelled lowering** (the reference's "bounded shortcut test",
discharged: `hn` and `hc` of `Normalizer.norm_fixed_nodup` hold on the actual lowered support). -/
theorem one_eq_reverse (yi : Fin (C10SupplierRowInput.liveList (Packets.live F)).length) :
    Packets.one a F g row yi = ((Packets.lowered a F row).map (List.map (relabel a F g yi))).reverse := by
  have hN := lowered_normal a F row
  have hV := lowered_valid a F row
  have hinj : ∀ x ∈ Packets.lowered a F row, ∀ y ∈ Packets.lowered a F row,
      List.map (relabel a F g yi) x = List.map (relabel a F g yi) y → x = y := by
    intro x hx y hy he
    have hv := congrArg (List.map Fin.val) he
    simp only [List.map_map] at hv
    have hx' : List.map (Fin.val ∘ relabel a F g yi) x = List.map (fun c => childCount a F * yi.val + c + 1) x :=
      List.map_congr_left (fun c hc => relabel_val a F g yi c (hV x hx c hc))
    have hy' : List.map (Fin.val ∘ relabel a F g yi) y = List.map (fun c => childCount a F * yi.val + c + 1) y :=
      List.map_congr_left (fun c hc => relabel_val a F g yi c (hV y hy c hc))
    rw [hx', hy'] at hv
    exact (List.map_injective_iff.mpr (fun u v huv => by simpa using huv)) hv
  have hn : ((Packets.lowered a F row).map (List.map (relabel a F g yi))).Nodup :=
    List.Nodup.map_on hinj hN.1
  have hc : ∀ m ∈ (Packets.lowered a F row).map (List.map (relabel a F g yi)), Ring.canon m = m := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    apply canon_eq
    rw [List.pairwise_map]
    refine (hN.2 x hx).imp_of_mem ?_
    intro u v hu hv huv
    show (relabel a F g yi u).val < (relabel a F g yi v).val
    rw [relabel_val a F g yi u (hV x hx u hu), relabel_val a F g yi v (hV x hx v hv)]
    omega
  unfold Packets.one
  exact PCJ6ffe03e3512f426d.Normalizer.norm_fixed_nodup _ hn hc

theorem rawWord_one (yi : Fin (C10SupplierRowInput.liveList (Packets.live F)).length) :
    ExtIncidence.P1CompactNativeFamily.rawWord (Packets.one a F g row yi) =
      P1Closure.RawRelabelFamily.emit (childCount a F) (Packets.lowered a F row).reverse yi.val := by
  rw [one_eq_reverse]
  unfold ExtIncidence.P1CompactNativeFamily.rawWord P1Closure.RawRelabelFamily.emit ExtIncidence.rawIndices
  congr 1
  rw [List.map_reverse, List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m hm
  simp only [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  intro c hc
  exact relabel_val a F g yi c (lowered_valid a F row m hm c hc)

theorem ofFn_range {n : ℕ} (h : ℕ → List Bool) :
    (List.ofFn (fun i : Fin n => h i.val)) = (List.range n).map h := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem rowWord_relabel :
    PCJ38fbfed565f64139_Family.rawWord a F g row =
      (List.range (2 ^ (Packets.live F).card)).flatMap
        (P1Closure.RawRelabelFamily.emit (childCount a F) (Packets.lowered a F row).reverse) := by
  unfold PCJ38fbfed565f64139_Family.rawWord Packets.packets
  have hfun : (fun yi : Fin (C10SupplierRowInput.liveList (Packets.live F)).length =>
      ExtIncidence.P1CompactNativeFamily.rawWord (Packets.one a F g row yi)) =
      (fun yi => P1Closure.RawRelabelFamily.emit (childCount a F) (Packets.lowered a F row).reverse yi.val) :=
    funext (rawWord_one a F g row)
  rw [List.flatMap_def, List.map_ofFn, Function.comp_def, hfun, ofFn_range, List.flatMap_def,
    C10SupplierRowInput.liveList_length]

theorem relabel_writes_rowWord (S : ℕ) (tail out : List Bool)
    (hS : (ExtIncidence.stream (Packets.lowered a F row).reverse).length ≤ S) :
    Step P1Closure.RawRelabelFamily.machine
      (P1Closure.RawRelabelFamily.budget (childCount a F) (2 ^ (Packets.live F).card) S)
      (P1Closure.RawRelabelFamily.familyHeads out)
      (P1Closure.RawRelabelFamily.familyData (childCount a F) (2 ^ (Packets.live F).card) S 0
        (Packets.lowered a F row).reverse tail out)
      (P1Closure.RawRelabelFamily.familyHeads (out ++ PCJ38fbfed565f64139_Family.rawWord a F g row))
      (P1Closure.RawRelabelFamily.familyData (childCount a F) (2 ^ (Packets.live F).card) S
        (2 ^ (Packets.live F).card) (Packets.lowered a F row).reverse tail
        (out ++ PCJ38fbfed565f64139_Family.rawWord a F g row)) := by
  have h := P1Closure.RawRelabelFamily.run (childCount a F) (2 ^ (Packets.live F).card) S
    (Packets.lowered a F row).reverse tail out hS
  rw [rowWord_relabel]
  exact h

/-- The relabel loop's cost is a fixed polynomial (degree 4) in `N + 2^K + S`. -/
theorem relabel_budget_le (N Y S : ℕ) :
    P1Closure.RawRelabelFamily.budget N Y S ≤ 128 * ((N + Y + S + 1) * (N + Y + S + 1) *
      (N + Y + S + 1) * (N + Y + S + 1)) := by
  unfold P1Closure.RawRelabelFamily.budget P1Closure.RawRelabelFamily.bodyBudget
    P1Closure.RawRelabelUniform.budget P1Closure.RawRelabelUniform.capacity
    P1Closure.RawRelabelOffset.budget P1Closure.RawRelabelOffset.rawBudget
  set M := N + Y + S + 1 with hMdef
  have hN : N ≤ M := by omega
  have hY : Y ≤ M := by omega
  have hS : S ≤ M := by omega
  have hM : 1 ≤ M := by omega
  calc Y * (2 * (N * (2 * Y + 3) + 5) + 2 + 2 * ((2 * (N * Y + 1) + 4) * S) + 2 * (N * Y + 2) + 12 +
        2 * Y + 7 + 3) + 3
      ≤ M * (2 * (M * (2 * M + 3) + 5) + 2 + 2 * ((2 * (M * M + 1) + 4) * M) + 2 * (M * M + 2) + 12 +
        2 * M + 7 + 3) + 3 := by gcongr
    _ ≤ 128 * (M * M * M * M) := by
      have h2 : M ≤ M * M := Nat.le_mul_of_pos_left M hM
      have h3 : M * M ≤ M * M * M := Nat.le_mul_of_pos_right (M * M) hM
      have h4 : M * M * M ≤ M * M * M * M := Nat.le_mul_of_pos_right (M * M * M) hM
      nlinarith

end
end NearCubicWires.PacketsConstruction
