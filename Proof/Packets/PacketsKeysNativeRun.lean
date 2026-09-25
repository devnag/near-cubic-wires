import Proof.Packets.PacketsKeysNativeDefs

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys.Native
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys
noncomputable section

/-! ## Stream reading facts -/

theorem sf_mid (pre mid post : List Bool) (i : ℕ) (hi : i < mid.length) :
    sf (pre ++ mid ++ post) (pre.length + i + 1) = mid.getD i false := by
  rw [sf_succ, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hi]

/-- Reading `natWord x` sitting after `pre`. -/
theorem read_mid (pre post : List Bool) (x : ℕ) :
    ∀ i, i < (natWord x).length →
      sf (pre ++ natWord x ++ post) (pre.length + 1 + i) = (natWord x).getD i false := by
  intro i hi
  rw [show pre.length + 1 + i = pre.length + i + 1 by omega]
  exact sf_mid pre (natWord x) post i hi

theorem nbl_le (x : ℕ) : natBitLength x ≤ (natWord x).length := by
  rw [ReadNat.natWord_length]; omega

theorem nbl_le_self (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 x
  omega

/-! ## Setup, docked -/

/-- The start state, right after setup. -/
def s0 (w : List Bool) : NS where
  f0 := (RepairOrdinary.frame w).length
  out := 0
  sp := 1
  mp := 1
  fl := false
  tag := 0
  h := 0
  nc := 0
  sum := 0
  prod := 0
  b := 0
  p2 := 0
  k := 0
  ct := ctAfter 0

def setupD := RecoveryFocus.machine ![(0 : Fin 26), 2, 3, 4] (Setup.machine 8)

theorem setup_run (w : List Bool) :
    LRuns (8 * w.length) setupD (Setup.cost 8 w.length) (initRoles 26 w) (nv w (s0 w)) := by
  have h := (Setup.run 8 (by omega) w).dockK ![(0 : Fin 26), 2, 3, 4] (by decide) (initRoles 26 w)
    (by intro j; fin_cases j <;> rfl) [0, 1, 2, 3] (by intro j hj; fin_cases j <;> simp at hj)
  refine h.weaken ?_
  intro i H A hi
  fin_cases i
  all_goals first
    | exact hi
    | (refine ⟨hi.1, fun j _ _ => ?_⟩; rw [hi.2 j]; simp [blank, s0])
    | (refine ⟨hi.1, ?_⟩; rw [hi.2 0]; simp [blank, s0])

/-! ## The front: tag, the constant `2`, the kind test -/

def front :=
  Composition.machine setupD
    (Composition.machine (ReadNat.at5 (4 : Fin 26) 2 3 5 8)
      (Composition.machine (swAt addF true true (4 : Fin 26) 17 7 6)
        (Composition.machine (swAt addF true true (4 : Fin 26) 17 7 6) (swAt subF false false (4 : Fin 26) 8 17 6))))

def frontCost (W n : ℕ) : ℕ :=
  Setup.cost 8 n + 1 + ((3 * W + 5) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3))))

/-- After the front: `tag` read, `k = 2`, `flag = tag < 2`. -/
def sF (w : List Bool) (t : ℕ) : NS :=
  { s0 w with sp := 1 + (natWord t).length, mp := 1 + (natWord t).length, tag := t, k := 2,
               fl := decide (t < 2) }

theorem front_run (w post : List Bool) (t : ℕ) (hw : w = natWord t ++ post) (ht : t ≤ 2)
    (hW : 1 ≤ w.length) :
    LRuns (8 * w.length) front (frontCost (8 * w.length) w.length) (initRoles 26 w) (nv w (sF w t)) := by
  have hW2 : 4 ≤ 2 ^ (8 * w.length) := by
    have : 2 ^ 2 ≤ 2 ^ (8 * w.length) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hlen : natBitLength t ≤ 8 * w.length := by
    have h1 := nbl_le t
    have h2 : (natWord t).length ≤ w.length := by rw [hw, List.length_append]; omega
    omega
  have e1 := setup_run w
  have e2 := readTag (W := 8 * w.length) w (s0 w) t rfl hlen (by
    intro i hi
    have := read_mid [] post t i hi
    simp only [List.nil_append, List.length_nil] at this
    rw [hw]
    exact this)
  have e3 := incK (W := 8 * w.length) w
    { s0 w with sp := 1 + (natWord t).length, mp := 1 + (natWord t).length, tag := t } (by
      show 0 + 1 < _
      omega)
  have e4 := incK (W := 8 * w.length) w
    { s0 w with sp := 1 + (natWord t).length, mp := 1 + (natWord t).length, tag := t, k := 0 + 1,
                fl := false } (by
      show 0 + 1 + 1 < _
      omega)
  have e5 := ltTag (W := 8 * w.length) w
    { s0 w with sp := 1 + (natWord t).length, mp := 1 + (natWord t).length, tag := t, k := 0 + 1 + 1,
                fl := false } (by
      show t < _
      omega) (by
      show 0 + 1 + 1 < _
      omega)
  exact e1.seq (e2.seq (e3.seq (e4.seq e5)))

/-! ## The header: `q`, `L`, `target` (discarded), `n`; then `k := 1` and `flag = tag < 1` -/

theorem read_at (w pre post : List Bool) (x : ℕ) (hw : w = pre ++ natWord x ++ post) (p : ℕ)
    (hp : p = pre.length + 1) :
    ∀ i, i < (natWord x).length → sf w (p + i) = (natWord x).getD i false := by
  intro i hi
  rw [hw, hp]
  exact read_mid pre post x i hi

theorem nbl_in (w pre post : List Bool) (x : ℕ) (hw : w = pre ++ natWord x ++ post) :
    natBitLength x ≤ 8 * w.length := by
  have h1 := nbl_le x
  have h2 : (natWord x).length ≤ w.length := by rw [hw]; simp only [List.length_append]; omega
  omega

def header :=
  Composition.machine (ReadNat.at5 (4 : Fin 26) 2 3 5 9)
    (Composition.machine (ReadNat.at5 (4 : Fin 26) 2 3 5 9)
      (Composition.machine (ReadNat.at5 (4 : Fin 26) 2 3 5 9)
        (Composition.machine (ReadNat.at5 (4 : Fin 26) 2 3 5 10)
          (Composition.machine (swAt subF true true (4 : Fin 26) 17 7 6)
            (swAt subF false false (4 : Fin 26) 8 17 6)))))

def headerCost (W : ℕ) : ℕ :=
  (3 * W + 5) + 1 + ((3 * W + 5) + 1 + ((3 * W + 5) + 1 + ((3 * W + 5) + 1 + ((2 * W + 3) + 1 + (2 * W + 3)))))

/-- The header's word. -/
def hdr (t q L tg n : ℕ) : List Bool := natWord t ++ natWord q ++ natWord L ++ natWord tg ++ natWord n

/-- After the header. -/
def sH (w : List Bool) (t q L tg n : ℕ) : NS :=
  { sF w t with sp := 1 + (hdr t q L tg n).length, mp := 1 + (hdr t q L tg n).length, h := tg, nc := n, k := 1,
                fl := decide (t < 1) }

theorem header_run (w rest : List Bool) (t q L tg n : ℕ) (hw : w = hdr t q L tg n ++ rest) (ht : t < 2) :
    LRuns (8 * w.length) header (headerCost (8 * w.length)) (nv w (sF w t)) (nv w (sH w t q L tg n)) := by
  unfold hdr at hw
  have hW2 : 4 ≤ 2 ^ (8 * w.length) := by
    have hl : 1 ≤ w.length := by
      rw [hw]; simp [ReadNat.natWord_length]
      omega
    have : 2 ^ 2 ≤ 2 ^ (8 * w.length) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have w1 : w = natWord t ++ natWord q ++ (natWord L ++ natWord tg ++ natWord n ++ rest) := by
    rw [hw]; simp only [List.append_assoc]
  have w2 : w = (natWord t ++ natWord q) ++ natWord L ++ (natWord tg ++ natWord n ++ rest) := by
    rw [hw]; simp only [List.append_assoc]
  have w3 : w = (natWord t ++ natWord q ++ natWord L) ++ natWord tg ++ (natWord n ++ rest) := by
    rw [hw]; simp only [List.append_assoc]
  have w4 : w = (natWord t ++ natWord q ++ natWord L ++ natWord tg) ++ natWord n ++ rest := by
    rw [hw]
  have e1 := readH (W := 8 * w.length) w (sF w t) q rfl (nbl_in w _ _ q w1)
    (read_at w _ _ q w1 _ (by simp [sF, s0]; omega))
  have e2 := readH (W := 8 * w.length) w
    { sF w t with sp := (sF w t).sp + (natWord q).length, mp := (sF w t).sp + (natWord q).length, h := q }
    L rfl (nbl_in w _ _ L w2) (read_at w _ _ L w2 _ (by simp [sF, s0]; omega))
  have e3 := readH (W := 8 * w.length) w
    { sF w t with sp := (sF w t).sp + (natWord q).length + (natWord L).length,
                  mp := (sF w t).sp + (natWord q).length + (natWord L).length, h := L }
    tg rfl (nbl_in w _ _ tg w3) (read_at w _ _ tg w3 _ (by simp [sF, s0]; omega))
  have e4 := readN (W := 8 * w.length) w
    { sF w t with sp := (sF w t).sp + (natWord q).length + (natWord L).length + (natWord tg).length,
                  mp := (sF w t).sp + (natWord q).length + (natWord L).length + (natWord tg).length, h := tg }
    n rfl (nbl_in w _ _ n w4) (read_at w _ _ n w4 _ (by simp [sF, s0]; omega))
  have e5 := decK (W := 8 * w.length) w
    { sF w t with sp := (sF w t).sp + (natWord q).length + (natWord L).length + (natWord tg).length +
                          (natWord n).length,
                  mp := (sF w t).sp + (natWord q).length + (natWord L).length + (natWord tg).length +
                          (natWord n).length, h := tg, nc := n } (by
      show 2 < _
      omega) (by
      show 1 ≤ 2
      omega)
  have e6 := ltTag (W := 8 * w.length) w
    { sF w t with sp := (sF w t).sp + (natWord q).length + (natWord L).length + (natWord tg).length +
                          (natWord n).length,
                  mp := (sF w t).sp + (natWord q).length + (natWord L).length + (natWord tg).length +
                          (natWord n).length, h := tg, nc := n, k := 2 - 1, fl := false } (by
      show t < _
      omega) (by
      show 2 - 1 < _
      omega)
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  have hp : (sF w t).sp + (natWord q).length + (natWord L).length + (natWord tg).length + (natWord n).length =
      1 + (natWord t ++ natWord q ++ natWord L ++ natWord tg ++ natWord n).length := by
    simp [sF, s0]; omega
  unfold sH hdr
  rw [← hp]
  exact hall

/-! ## The circuit chain -/

section Chain
variable {α : Type} (L : List α) (F : α → List Bool) (g : α → ℕ)

theorem sum_take_le (k : ℕ) : ((L.take k).map g).sum ≤ (L.map g).sum := by
  have h := congrArg List.sum (congrArg (List.map g) (List.take_append_drop k L))
  rw [List.map_append, List.sum_append] at h
  omega

theorem prod_take_le (hg : ∀ a ∈ L, 1 ≤ g a) (k : ℕ) : ((L.take k).map g).prod ≤ (L.map g).prod := by
  have h := congrArg List.prod (congrArg (List.map g) (List.take_append_drop k L))
  rw [List.map_append, List.prod_append] at h
  have hp : 0 < ((L.drop k).map g).prod := by
    apply List.prod_pos_iff_forall_pos_nat.mpr
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact hg x (List.mem_of_mem_drop hx)
  rw [← h]
  exact Nat.le_mul_of_pos_right _ hp

theorem take_succ_of_lt (c : ℕ) (hc : c < L.length) : L.take (c + 1) = L.take c ++ [L[c]] :=
  List.take_succ_eq_append_getElem hc

theorem flatMap_split (c : ℕ) (hc : c < L.length) :
    L.flatMap F = (L.take c).flatMap F ++ F L[c] ++ (L.drop (c + 1)).flatMap F := by
  have e : L = L.take c ++ [L[c]] ++ L.drop (c + 1) := by
    rw [← take_succ_of_lt L c hc, List.take_append_drop]
  conv_lhs => rw [e]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

end Chain

/-- The chain state after `c` circuit blocks. -/
def chainSt {α : Type} (S0 : NS) (pre : List Bool) (L : List α) (F : α → List Bool) (g : α → ℕ) (c bb pp : ℕ) :
    NS :=
  { S0 with
    sp := 1 + pre.length + ((L.take c).flatMap F).length,
    sum := ((L.take c).map g).sum,
    prod := ((L.take c).map g).prod,
    ct := ctAfter c, fl := false, b := bb, p2 := pp }

/-- **One circuit block of the chain.** The stream word is `pre ++ L.flatMap (frame ∘ pay)`; every payload
starts with `natWord (num a)`. -/
theorem block_step {α : Type} {W : ℕ} (w pre : List Bool) (L : List α) (pay : α → List Bool) (num : α → ℕ)
    (hw : w = pre ++ L.flatMap (fun a => RepairOrdinary.frame (pay a)))
    (hpay : ∀ a, ∃ rest, pay a = natWord (num a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ W) (hW1 : 1 ≤ W)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ W) (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ W)
    (S0 : NS) (c : Fin 4) (bb pp m : ℕ) (hm : w.length ≤ m) :
    ∃ bb' pp', LRuns W (block c) (blockCost W m)
      (nv w (chainSt S0 pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) c.val bb pp))
      (nv w (chainSt S0 pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) (c.val + 1) bb' pp')) := by
  set F : α → List Bool := fun a => RepairOrdinary.frame (pay a) with hF
  set g : α → ℕ := fun a => num a + 1 with hg
  by_cases hc : c.val < L.length
  · -- a circuit is present
    obtain ⟨rest, hr⟩ := hpay L[c.val]
    have hsplit := flatMap_split L F c.val hc
    have hpl : (pay L[c.val]).length ≤ m := by
      have h1 : (F L[c.val]).length ≤ w.length := by
        rw [hw, hsplit]; simp only [List.length_append]; omega
      have h2 : (F L[c.val]).length = 2 * (pay L[c.val]).length + 1 := RepairOrdinary.frame_length _
      omega
    have hX : ∀ i, i < (RepairOrdinary.frame (pay L[c.val])).length →
        sf w ((chainSt S0 pre L F g c.val bb pp).sp + i) = (RepairOrdinary.frame (pay L[c.val])).getD i false := by
      intro i hi
      have e : w = (pre ++ (L.take c.val).flatMap F) ++ F L[c.val] ++ (L.drop (c.val + 1)).flatMap F := by
        rw [hw, hsplit]; simp only [List.append_assoc]
      have := sf_mid (pre ++ (L.take c.val).flatMap F) (F L[c.val]) ((L.drop (c.val + 1)).flatMap F) i hi
      rw [e]
      convert this using 2
      simp only [chainSt, List.length_append]
      omega
    have hsum1 := sum_take_le L g (c.val + 1)
    have hprod1 := prod_take_le L g (fun a _ => by simp [hg]) (c.val + 1)
    rw [take_succ_of_lt L c.val hc, List.map_append, List.sum_append] at hsum1
    rw [take_succ_of_lt L c.val hc, List.map_append, List.prod_append] at hprod1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil,
      Nat.add_zero, Nat.mul_one] at hsum1 hprod1
    have hx : num L[c.val] + 1 < 2 ^ W := by
      show g L[c.val] < 2 ^ W
      have := lt_of_le_of_lt hsum1 hsumB
      omega
    refine ⟨num L[c.val] + 1, ((L.take c.val).map g).prod * (num L[c.val] + 1), ?_⟩
    have h := block_present (W := W) w (chainSt S0 pre L F g c.val bb pp) c (pay L[c.val]) rest (num L[c.val]) hr hX
      rfl (hnb _ (List.getElem_mem hc)) hW1 hx (by
        show ((L.take c.val).map g).sum + g L[c.val] < 2 ^ W
        exact lt_of_le_of_lt hsum1 hsumB)
      (by
        show ((L.take c.val).map g).prod * g L[c.val] < 2 ^ W
        exact lt_of_le_of_lt hprod1 hprodB)
    refine (h.enlarge (by unfold blockCost bodyCost; omega)).congr_out ?_
    congr 1
    simp only [bodyOut, rbS, uf, chainSt, take_succ_of_lt L c.val hc, List.flatMap_append, List.map_append,
      List.sum_append, List.prod_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil, List.append_nil]
    simp only [hF, hg]
    congr 1 <;> ring
  · -- no circuit left: the stream is past its end
    have hle : L.length ≤ c.val := by omega
    have htake : L.take c.val = L := List.take_of_length_le hle
    have htake1 : L.take (c.val + 1) = L := List.take_of_length_le (by omega)
    have hbit : sf w (chainSt S0 pre L F g c.val bb pp).sp = false := by
      simp only [chainSt, htake]
      rw [show 1 + pre.length + (L.flatMap F).length = (pre.length + (L.flatMap F).length) + 1 by omega, sf_succ]
      apply List.getD_eq_default
      rw [hw]; simp
    refine ⟨bb, pp, ?_⟩
    have h := block_absent (W := W) w (chainSt S0 pre L F g c.val bb pp) c m hbit rfl
    refine h.congr_out ?_
    simp only [chainSt, htake, htake1]

end
end NearCubicWires.PacketsKeys.Native

