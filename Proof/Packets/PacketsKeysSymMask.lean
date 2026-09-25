import Proof.Packets.PacketsKeysStageOn
import Proof.Packets.PacketsSymMaskProg

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsKeys.Stage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsMeta NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsSymBits
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## The SYM mask word -/

theorem mpx_gt (bs : List ℕ) (j : ℕ) : ∀ i, j < i → mpx bs j i = List.replicate bs.sum false := by
  induction bs with
  | nil => intro i _; rfl
  | cons b bs ih =>
    intro i hi
    simp only [mpx, List.sum_cons, List.replicate_add]
    rw [ih (i + 1) (by omega), show decide (i = j) = false by simp; omega]

theorem mpx_blocks (bs : List ℕ) : ∀ (j i : ℕ), i ≤ j → j < i + bs.length →
    mpx bs j i = List.replicate ((bs.take (j - i)).sum) false ++ List.replicate (bs.getD (j - i) 0) true ++
      List.replicate ((bs.drop (j - i + 1)).sum) false := by
  induction bs with
  | nil => intro j i h1 h2; simp at h2; omega
  | cons b bs ih =>
    intro j i h1 h2
    simp only [mpx]
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h
      rw [mpx_gt bs i (i + 1) (by omega), Nat.sub_self]
      simp
    · have hlen : j < (i + 1) + bs.length := by simp at h2; omega
      rw [ih j (i + 1) (by omega) hlen, show decide (i = j) = false by simp; omega]
      obtain ⟨d, hd⟩ : ∃ d, j - i = d + 1 := ⟨j - i - 1, by omega⟩
      rw [hd, show j - (i + 1) = d by omega]
      rw [List.take_succ_cons, List.sum_cons, List.replicate_add, List.getD_cons_succ, List.drop_succ_cons]
      simp only [List.append_assoc]

/-! ## A list segment's mask as three blocks -/

theorem mem_mask_iff {α : Type} {all : List α} (s : ListSegment all) (o : Fin all.length) :
    o ∈ s.mask ↔ s.before.length ≤ o.val ∧ o.val < s.before.length + s.body.length := by
  unfold ListSegment.mask
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x, _, hx⟩
    have hv := congrArg Fin.val hx
    rw [ListSegment.embedding_val] at hv
    have := x.isLt
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨o.val - s.before.length, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rw [ListSegment.embedding_val]
    simp only
    omega

theorem seg_bits {α : Type} {all : List α} (s : ListSegment all) :
    List.ofFn (fun o : Fin all.length => decide (o ∈ s.mask)) =
      List.replicate s.before.length false ++ List.replicate s.body.length true ++
        List.replicate s.after.length false := by
  have hlen := congrArg List.length s.decomposition
  simp only [List.length_append] at hlen
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro n h1 h2
    rw [List.getElem_ofFn]
    have hm := mem_mask_iff s ⟨n, by simpa using h1⟩
    simp only at hm
    by_cases a1 : n < s.before.length
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_replicate]
      simp only [decide_eq_false_iff_not]
      rw [hm]; omega
    · by_cases a2 : n < s.before.length + s.body.length
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega),
          List.getElem_replicate]
        simp only [decide_eq_true_eq]
        rw [hm]; omega
      · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate]
        simp only [decide_eq_false_iff_not]
        rw [hm]; omega

/-! ## Mask `j` of a SYM request -/

theorem symOcc_length {q : ℕ} (l : List (NormalizedSymmetricThresholdCircuit q)) :
    (l.flatMap symmetricCircuitOccurrences).length = (l.map (fun c => c.bottomCount)).sum := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [List.flatMap_cons, ih, symmetricCircuitOccurrences]

theorem sym_bits (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : rcKey a (.sym r four L target)) (j : ℕ)
    (hj : j < r.circuits.length) :
    (maskBitsList a (.sym r four L target) k).getD j [] = mpx (r.circuits.map (fun c => c.bottomCount)) j 0 := by
  have hl : j < (symMasks r).length := by simp [symMasks]; exact hj
  simp only [maskBitsList]
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
  simp only [symMasks, List.getElem_ofFn]
  unfold MaskCoord.maskBits symmetricCircuitMask
  rw [seg_bits, mpx_blocks _ j 0 (Nat.zero_le _) (by simp; exact hj), Nat.sub_zero]
  simp only [symmetricCircuitSegment, symOcc_length, List.map_take, List.map_drop]
  congr 2
  · congr 1
    simp only [symmetricCircuitOccurrences, List.length_ofFn, List.get_eq_getElem]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]

/-! ## Cost -/

theorem maskCost_le (m : ℕ) : maskCost (8 * m) m ≤ 20000 * (m + 1) ^ 2 := by
  unfold maskCost myBlockCost emitSelCost EmitK.cost Native.frontCost Native.headerCost Native.blockCost
    Native.bodyCost PacketsKeys.Setup.cost
  nlinarith [Nat.zero_le m]

/-! ## The stage -/

/-- The mask program's entry roles on a request's native word. -/
def symIn (a : DecompositionAlgorithm) (r : Request) (j : ℕ) : Fin (26 + 6) → TS :=
  Fin.addCases (PacketsKeys.initRoles 26 (fields a r 0)) (exIn j)

theorem symIn_blank (a : DecompositionAlgorithm) (r : Request) (j W : ℕ) (i : Fin (26 + 6)) (h0 : i ≠ 0)
    (h28 : i ≠ 28) : TR W (symIn a r j i) 0 [] := by
  unfold symIn
  induction i using Fin.addCases with
  | left i' =>
    rw [Fin.addCases_left]
    unfold PacketsKeys.initRoles
    have hi0 : i'.val ≠ 0 := by
      intro e
      exact h0 (Fin.ext (by simp [e]))
    rw [if_neg hi0]
    by_cases h1 : i'.val = 1
    · rw [if_pos h1]
      exact ⟨rfl, rfl⟩
    · rw [if_neg h1]
      exact ⟨rfl, fun j => read_nil j⟩
  | right i' =>
    rw [Fin.addCases_right]
    fin_cases i'
    · exact ⟨rfl, fun j => read_nil j⟩
    · exact ⟨rfl, fun j => read_nil j⟩
    · exact absurd rfl h28
    · exact ⟨rfl, read_nil 0⟩
    · exact ⟨rfl, read_nil 0⟩
    · exact ⟨rfl, read_nil 0⟩

/-- The SYM stage's per-request step bound. -/
def symPc (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  maskCost (8 * (fields a r 0).length) (fields a r 0).length + (fields a r 0).length + 16

theorem symPc_le (a : DecompositionAlgorithm) (r : Request) : symPc a r ≤ 20017 * (r.smallSize a) ^ 2 := by
  unfold symPc
  have h1 := maskCost_le (fields a r 0).length
  have h2 := Native.native_le_small a r
  have h3 : ((fields a r 0).length + 1) ^ 2 ≤ (r.smallSize a) ^ 2 := Nat.pow_le_pow_left h2 2
  have h4 : (fields a r 0).length + 16 ≤ 17 * ((fields a r 0).length + 1) ^ 2 := by nlinarith
  nlinarith

theorem sym_count (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : rcKey a (.sym r four L target)) :
    maskCount a (.sym r four L target) k = r.circuits.length := by
  rw [← maskBitsList_length]
  simp [maskBitsList, symMasks]

def symMask (a : DecompositionAlgorithm) : KeyStageOn a IsSym (fun r k j => (maskBitsList a r k).getD j []) :=
  KeyStageOn.ofProg (KVecOn.ofKeyWord IsSym (KeyWord.ofWord (fieldFrame a 0))) maskProg
    (fun _ => (0 : Fin (26 + 6))) 28 26 27
    (fun x y _ => Subsingleton.elim x y) (fun _ => by decide) (by decide)
    (fun r _ _ => 8 * (fields a r 0).length)
    (fun r _ _ => maskCost (8 * (fields a r 0).length) (fields a r 0).length)
    (fun r _ j => symIn a r j)
    (by
      intro r hp k hk j hj
      cases r with
      | terminal => exact hp.elim
      | thr _ _ _ _ => exact hp.elim
      | sym r0 four L target =>
        have hjc : j < r0.circuits.length := by rw [← sym_count a r0 four L target k]; exact hj
        have hfl : (r0.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))).length ≤
            (fields a (.sym r0 four L target) 0).length := by
          rw [Native.native_sym]; simp
        obtain ⟨b1, _, b3⟩ := Native.sym_bounds a r0 four L target
        have hpos := Native.len_pos a (.sym r0 four L target)
        have hlt := Native.small_lt _ hpos
        obtain ⟨σ', hl, h26, h27⟩ := maskProg_run r0.q L target r0.circuits symWord (fun c => c.bottomCount) j
          (fields a (.sym r0 four L target) 0) (Native.native_sym a r0 four L target) (fun c => Native.symWord_pay c)
          (by
            intro c hc
            have e1 := Native.nbl_le_self c.bottomCount
            have e2 := Native.bc_le c
            have e3 := Native.mem_len_le r0.circuits (fun c => RepairOrdinary.frame (symWord c)) c hc
            omega)
          (by omega) b3 b1 four
        rw [sym_bits a r0 four L target k j hjc]
        exact ⟨σ', hl, h26, h27⟩)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (by
      intro r k j i h0 h28
      exact symIn_blank a r j _ i (fun e => h0 0 e.symm) h28)
    (symPc a)
    (by
      intro r hp k hk j hj
      cases r with
      | terminal => exact hp.elim
      | thr _ _ _ _ => exact hp.elim
      | sym r0 four L target =>
        have hjc : j < r0.circuits.length := by rw [← sym_count a r0 four L target k]; exact hj
        obtain ⟨b1, _, _⟩ := Native.sym_bounds a r0 four L target
        have hv : ((maskBitsList a (.sym r0 four L target) k).getD j []).length ≤
            (fields a (.sym r0 four L target) 0).length := by
          rw [sym_bits a r0 four L target k j hjc, mpx_length]
          have := sum_map_le r0.circuits (fun c => c.bottomCount) (fun c => c.bottomCount + 1) (fun c => by omega)
          omega
        unfold symPc
        omega)
    20017 2 (symPc_le a)

end
end NearCubicWires.PacketsKeys.Stage

