import Proof.Packets.PacketsCombineLayout

/-! # P2 (ii) kit core: the SYM combine engine (ordered product of per-block one-hot lookups)

Consumer: `SymCombineStageK.run` (`Proof/Packets/PacketsRowPolySplitKit.lean`), whose tape-14 output is the kit
register of `(rcDecode a (.sym …) k).polynomial`, which is by `rfl` (`PacketsRowPolyPlan.sym_rowPoly`)
`Normalized.structuralGF2FiniteConjunction (fun i => structuralGF2OneHotLookup (lookup i) (coord i))`
= `Product (ofFn L)` = `foldr Ring.mul [[]] [L 0, …, L (n-1)]`, `L i = foldr Ring.add [] (terms of block i)`.
Paper: the row's canonical polynomial expansion is charged in `T_prep` (`paper.tex:1197-1200`);
budget class: source-polynomial (every cost below is a fixed polynomial in the kit reserve).

Algorithm (all machines REUSED; one new fixed composition): blocks are processed in DESCENDING
order `i = n-1, …, 0`, so the parked register runs through the suffix products
`foldr mul [[]] [L i, …, L (n-1)]`, exactly the frozen right fold. Per block:
segment fold (`segment_run`) → copy `acc → left` → copy `park → acc` → `acc := mul left acc`
(`OrderedPacketStep.multiply_run`) → copy `acc → park` → `acc := []` (`OrderedPacketReset.zero_run`).
The descending index/bit cursors of block `i` end exactly where block `i-1` starts.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

/-! ## Semantics -/

/-- The one-hot lookup of block `i` (bank entries and bits `[i*m, i*m+m)`). -/
def segPoly (ps : List Poly) (bits : List Bool) (m i : ℕ) : Poly :=
  (segTerms ps bits (i * m) m).foldr Ring.add []

/-- The blocks' lookups, in block order. -/
def blockPolys (ps : List Poly) (bits : List Bool) (n m : ℕ) : List Poly :=
  List.ofFn (fun i : Fin n => segPoly ps bits m i.val)

/-- The parked register after `j` blocks (the last `j` blocks' ordered product). -/
def parkAt (ps : List Poly) (bits : List Bool) (n m j : ℕ) : Poly :=
  ((blockPolys ps bits n m).drop (n - j)).foldr Ring.mul [[]]

/-- The left register after `j` blocks. -/
def leftAt (ps : List Poly) (bits : List Bool) (n m : ℕ) (left0 : Poly) (j : ℕ) : Poly :=
  if j = 0 then left0 else segPoly ps bits m (n - j)

theorem segPoly_bounded (S : Finset ℕ) (d : ℕ) (ps : List Poly) (bits : List Bool) (m i : ℕ)
    (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P) :
    NormalizedIntermediate.Bounded S d (segPoly ps bits m i) := by
  unfold segPoly
  have h := NormalizedIntermediate.parity_prefix (segTerms ps bits (i * m) m)
    (segTerms_bounded S d ps bits (i * m) m hps) (segTerms ps bits (i * m) m).length
  rw [← List.length_reverse, List.take_length, List.foldl_reverse] at h
  exact h

theorem parkAt_zero (ps : List Poly) (bits : List Bool) (n m : ℕ) : parkAt ps bits n m 0 = [[]] := by
  unfold parkAt
  rw [Nat.sub_zero, List.drop_of_length_le (by simp [blockPolys])]
  rfl

theorem parkAt_succ (ps : List Poly) (bits : List Bool) (n m j : ℕ) (hj : j < n) :
    parkAt ps bits n m (j + 1) = Ring.mul (segPoly ps bits m (n - (j + 1))) (parkAt ps bits n m j) := by
  unfold parkAt
  have hlen : (blockPolys ps bits n m).length = n := by simp [blockPolys]
  have hk : n - (j + 1) < (blockPolys ps bits n m).length := by omega
  rw [List.drop_eq_getElem_cons hk, List.foldr_cons]
  have he : n - (j + 1) + 1 = n - j := by omega
  rw [he]
  congr 1
  simp [blockPolys]

theorem parkAt_full (ps : List Poly) (bits : List Bool) (n m : ℕ) :
    parkAt ps bits n m n = Normalized.structuralGF2Product (blockPolys ps bits n m) := by
  unfold parkAt
  rw [Nat.sub_self, List.drop_zero]
  rfl

theorem parkAt_bounded (S : Finset ℕ) (d : ℕ) (ps : List Poly) (bits : List Bool) (n m j : ℕ)
    (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P) :
    NormalizedIntermediate.Bounded S (d * n) (parkAt ps bits n m j) := by
  unfold parkAt
  have hall : ∀ P ∈ (blockPolys ps bits n m).drop (n - j), NormalizedIntermediate.Bounded S d P := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hP)
    exact segPoly_bounded S d ps bits m i.val hps
  have h := NormalizedIntermediate.product _ hall
  apply NormalizedIntermediate.mono h
  apply Nat.mul_le_mul_left
  simp [blockPolys]

/-! ## Registers fit the reserve -/

theorem reg_lengths (C w : ℕ) (P : Poly) (hP : P.length ≤ 2 ^ w) :
    (ZeroPadding.pad (commonReserve C w) (P.map (maskNat C)).flatten).length = commonReserve C w ∧
    (ZeroPadding.pad (commonReserve C w) (CompareMachine.word P.length)).length = commonReserve C w := by
  have hf := (SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C P)
    (by simpa only [List.length_map] using hP)).2
  refine ⟨VectorAccumulator.flat_length _ _ hf, ?_⟩
  have h := VectorAccumulator.count_length _ _ hf
  simpa only [List.length_map] using h

theorem reg_count_map (C w : ℕ) (P : Poly) (hP : P.length ≤ 2 ^ w) :
    (ZeroPadding.pad (commonReserve C w) (CompareMachine.word (P.map (maskNat C)).length)).length =
      commonReserve C w := by
  rw [List.length_map]
  exact (reg_lengths C w P hP).2

/-! ## Machines -/

/-- An arena (37-tape) machine lifted into the combine layout. -/
def emb37 {s : ℕ} (p : Machine 37 s) := TapeEmbedding.machine 2 (TapeEmbedding.machine 1 (TapeEmbedding.machine 1 p))

theorem emb37_run {s n : ℕ} {p : Machine 37 s} (C R index N pos : ℕ) (left acc left' acc' : Poly)
    (ps : List Poly) (bits : List Bool) (P : Poly)
    (h : Step p n (ArithmeticLookup.H 0) (OrderedPacketStep.A C R index left acc ps)
      (ArithmeticLookup.H 0) (OrderedPacketStep.A C R index left' acc' ps)) :
    Step (emb37 p) n (bodyH pos) (bodyA C R index N left acc ps bits P)
      (bodyH pos) (bodyA C R index N left' acc' ps bits P) :=
  ((h.embed (fun _ : Fin 1 => pos) (fun _ => bits)).embed (fun _ : Fin 1 => 1)
    (fun _ => CompareMachine.word N)).embed (fun _ : Fin 2 => 0) (parkWords C R P)

def foldM := TapeEmbedding.machine 2 TranscriptColumnLookupFold.machine
def copyAccLeft := PhysicalCopyPair.machine (t := 41) 31 26 25 27 28
def copyParkAcc := PhysicalCopyPair.machine (t := 41) 31 39 26 40 27
def copyAccPark := PhysicalCopyPair.machine (t := 41) 31 26 39 27 40

/-- One block of the SYM combine. -/
def symBody := Composition.machine foldM (Composition.machine copyAccLeft (Composition.machine copyParkAcc
  (Composition.machine (emb37 OrderedPacketStep.multiply) (Composition.machine copyAccPark
    (emb37 OrderedPacketReset.zeroMachine)))))

def symBodyBudget (C w m : ℕ) : ℕ :=
  TranscriptColumnLookupFold.budget C w m + 1 + ((4 * commonReserve C w + 5) + 1 +
    ((4 * commonReserve C w + 5) + 1 + (ReusableArithmetic.boundedBudget C w + 1 +
      ((4 * commonReserve C w + 5) + 1 + (4 * commonReserve C w + 5)))))

theorem copy_run (C R base m : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly)
    (s1 t1 s2 t2 : Fin 41) (hne1 : s1 ≠ t1) (hne2 : s2 ≠ t2) (hsurv : s2 ≠ t1) (htgt : t2 ≠ t1)
    (hs1 : bodyH base s1 = 0) (ht1 : bodyH base t1 = 0) (hs2 : bodyH base s2 = 0) (ht2 : bodyH base t2 = 0)
    (l1 : (bodyA C R base m left acc ps bits P s1).length = R)
    (l2 : (bodyA C R base m left acc ps bits P t1).length = R)
    (l3 : (bodyA C R base m left acc ps bits P s2).length = R)
    (l4 : (bodyA C R base m left acc ps bits P t2).length = R) :
    Step (PhysicalCopyPair.machine (t := 41) 31 s1 t1 s2 t2) (4 * R + 5) (bodyH base)
      (bodyA C R base m left acc ps bits P) (bodyH base)
      (Function.update (Function.update (bodyA C R base m left acc ps bits P) t1
        (bodyA C R base m left acc ps bits P s1)) t2 (bodyA C R base m left acc ps bits P s2)) :=
  PhysicalCopyPair.run R 31 s1 t1 s2 t2 (bodyH base) (bodyA C R base m left acc ps bits P)
    hne1 hne2 hsurv htgt rfl hs1 ht1 hs2 ht2 rfl l1 l2 l3 l4

/-- **One block.** From index/bit cursor `base+m`, empty accumulator and parked `P`, the block's
lookup `L` is computed, `P` becomes `mul L P`, the accumulator is empty again, the cursors are at
`base`, and `left = L`. -/
theorem symBody_run (C w : ℕ) (S : Finset ℕ) (d : ℕ) (ps : List Poly) (bits : List Bool)
    (base m : ℕ) (left P : Poly)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hseg : base + m ≤ ps.length) (hN : ps.length ≤ 2 ^ w)
    (hl : left.length ≤ 2 ^ w) (hPf : Fits C P) (hPc : P.length ≤ 2 ^ w)
    (hLP : (Ring.mul ((segTerms ps bits base m).foldr Ring.add []) P).length ≤ 2 ^ w) (hw : 1 ≤ w) :
    Step symBody (symBodyBudget C w m) (bodyH (base + m))
      (bodyA C (commonReserve C w) (base + m) m left [] ps bits P) (bodyH base)
      (bodyA C (commonReserve C w) base m ((segTerms ps bits base m).foldr Ring.add []) [] ps bits
        (Ring.mul ((segTerms ps bits base m).foldr Ring.add []) P)) := by
  set R := commonReserve C w with hRdef
  set L := (segTerms ps bits base m).foldr Ring.add [] with hLdef
  have hLb : NormalizedIntermediate.Bounded S d L := by
    have h := NormalizedIntermediate.parity_prefix (segTerms ps bits base m)
      (segTerms_bounded S d ps bits base m hps) (segTerms ps bits base m).length
    rw [← List.length_reverse, List.take_length, List.foldl_reverse] at h
    exact h
  have hLc : L.length ≤ 2 ^ w := (NormalizedIntermediate.census hLb).trans hfit
  have hLf : Fits C L := SubstitutionCensus.fits_of_bounded C S hS hLb
  set last := OrderedPacketFold.last (segTerms ps bits base m) left m with hlastdef
  have hlastc : last.length ≤ 2 ^ w := by
    apply OrderedPacketFold.last_count _ _ (2 ^ w) m hl
    intro Q hQ
    exact (NormalizedIntermediate.census (segTerms_bounded S d ps bits base m hps Q hQ)).trans hfit
  -- 1. the segment fold
  have s1 := (segment_run C w S d ps left bits base m hS hps hfit hseg hN hl hw).embed
    (fun _ : Fin 2 => 0) (parkWords C R P)
  change Step foldM _ (bodyH (base + m)) (bodyA C R (base + m) m left [] ps bits P) (bodyH base)
    (bodyA C R base m last L ps bits P) at s1
  -- 2. acc → left
  have s2 := copy_run C R base m last L ps bits P 26 25 27 28 (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl (reg_lengths C w L hLc).1 (reg_lengths C w last hlastc).1 (reg_count_map C w L hLc)
    (reg_count_map C w last hlastc)
  rw [bodyA_acc_to_left] at s2
  -- 3. park → acc
  have s3 := copy_run C R base m L L ps bits P 39 26 40 27 (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl (reg_lengths C w P hPc).1 (reg_lengths C w L hLc).1 (reg_lengths C w P hPc).2
    (reg_count_map C w L hLc)
  rw [bodyA_park_to_acc] at s3
  -- 4. acc := mul left acc
  have s4 := emb37_run C R base m base L P L (Ring.mul L P) ps bits P
    (OrderedPacketStep.multiply_run C w base L P ps hLf hPf hLc hPc hw)
  -- 5. acc → park
  have s5 := copy_run C R base m L (Ring.mul L P) ps bits P 26 39 27 40 (by decide) (by decide) (by decide)
    (by decide) rfl rfl rfl rfl (reg_lengths C w _ hLP).1 (reg_lengths C w P hPc).1 (reg_count_map C w _ hLP)
    (reg_lengths C w P hPc).2
  rw [bodyA_acc_to_park] at s5
  -- 6. acc := []
  have s6 := emb37_run C R base m base L (Ring.mul L P) L [] ps bits (Ring.mul L P)
    (OrderedPacketReset.zero_run C w base L (Ring.mul L P) ps hLP)
  exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))

/-! ## The whole block loop -/

/-- The SYM combine loop: `symBody` repeated once per block, driven by `word n`. -/
def symLoop := RepeatMachine.machine symBody (fun _ _ => true)

theorem block_index (n m j : ℕ) (hj : j < n) : (n - (j + 1)) * m + m = (n - j) * m := by
  have e : n - j = n - (j + 1) + 1 := by omega
  rw [e, Nat.succ_mul]

/-- **The SYM loop.** From cursor `n*m`, empty accumulator and parked `[[]]`, the parked register
ends as the ordered product `Product [L 0, …, L (n-1)]` of the blocks' one-hot lookups; the
cursors end at `0`, the accumulator is empty, and the bank, bits and drivers are unchanged. -/
theorem symLoop_run (C w : ℕ) (S : Finset ℕ) (d : ℕ) (ps : List Poly) (bits : List Bool)
    (n m : ℕ) (left0 : Poly)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hfitn : (S.card + 1) ^ (d * n) ≤ 2 ^ w)
    (hlen : n * m ≤ ps.length) (hN : ps.length ≤ 2 ^ w) (hl0 : left0.length ≤ 2 ^ w) (hw : 1 ≤ w) :
    Step symLoop (n * (symBodyBudget C w m + 3) + 3)
      (Fin.addCases (m := 41) (n := 1) (motive := fun _ => ℕ) (bodyH (n * m)) (fun _ => 1))
      (Fin.addCases (m := 41) (n := 1) (motive := fun _ => List Bool)
        (bodyA C (commonReserve C w) (n * m) m left0 [] ps bits [[]]) (fun _ => CompareMachine.word n))
      (Fin.addCases (m := 41) (n := 1) (motive := fun _ => ℕ) (bodyH 0) (fun _ => 1))
      (Fin.addCases (m := 41) (n := 1) (motive := fun _ => List Bool)
        (bodyA C (commonReserve C w) 0 m (leftAt ps bits n m left0 n) [] ps bits
          (Normalized.structuralGF2Product (blockPolys ps bits n m))) (fun _ => CompareMachine.word n)) := by
  let hs : ℕ → Fin 41 → ℕ := fun j => bodyH ((n - j) * m)
  let as : ℕ → Fin 41 → List Bool := fun j => bodyA C (commonReserve C w) ((n - j) * m) m
    (leftAt ps bits n m left0 j) [] ps bits (parkAt ps bits n m j)
  have hpark : ∀ j, (parkAt ps bits n m j).length ≤ 2 ^ w := fun j =>
    (NormalizedIntermediate.census (parkAt_bounded S d ps bits n m j hps)).trans hfitn
  have body : ∀ j, j < n → Step symBody (symBodyBudget C w m) (hs j) (as j) (hs (j + 1)) (as (j + 1)) := by
    intro j hj
    have hleft : (leftAt ps bits n m left0 j).length ≤ 2 ^ w := by
      unfold leftAt
      split
      · exact hl0
      · exact (NormalizedIntermediate.census (segPoly_bounded S d ps bits m _ hps)).trans hfit
    have hmul : (Ring.mul ((segTerms ps bits ((n - (j + 1)) * m) m).foldr Ring.add [])
        (parkAt ps bits n m j)).length ≤ 2 ^ w := by
      have h := hpark (j + 1)
      rw [parkAt_succ ps bits n m j hj] at h
      exact h
    have hb := block_index n m j hj
    have run := symBody_run C w S d ps bits ((n - (j + 1)) * m) m (leftAt ps bits n m left0 j)
      (parkAt ps bits n m j) hS hps hfit
      (by rw [hb]; exact (Nat.mul_le_mul_right m (Nat.sub_le n j)).trans hlen) hN hleft
      (SubstitutionCensus.fits_of_bounded C S hS (parkAt_bounded S d ps bits n m j hps)) (hpark j) hmul hw
    rw [hb] at run
    have hl1 : leftAt ps bits n m left0 (j + 1) =
        (segTerms ps bits ((n - (j + 1)) * m) m).foldr Ring.add [] := by
      unfold leftAt segPoly
      rw [if_neg (Nat.succ_ne_zero j)]
    have hp1 := parkAt_succ ps bits n m j hj
    unfold segPoly at hp1
    dsimp only [hs, as]
    rw [hl1, hp1]
    exact run
  have result := PhysicalRepeatStep.run symBody n (symBodyBudget C w m) hs as body
  dsimp only [hs, as] at result
  rw [Nat.sub_zero, Nat.sub_self, Nat.zero_mul, parkAt_zero, parkAt_full] at result
  have h0 : leftAt ps bits n m left0 0 = left0 := by simp [leftAt]
  rw [h0] at result
  exact result

end
end NearCubicWires.PacketsCombine
