import Proof.Packets.PacketsKeysNativeStages
import Proof.Packets.PacketsSymExact

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsSymBits
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys
noncomputable section

/-! ## The mask word -/

/-- `concat_i replicate b_i (i + i0 = j)`. -/
def mpx : List ℕ → ℕ → ℕ → List Bool
  | [], _, _ => []
  | b :: bs, j, i => List.replicate b (decide (i = j)) ++ mpx bs j (i + 1)

theorem mpx_snoc (xs : List ℕ) (b j : ℕ) : ∀ i, mpx (xs ++ [b]) j i =
    mpx xs j i ++ List.replicate b (decide (i + xs.length = j)) := by
  induction xs with
  | nil => intro i; simp [mpx]
  | cons x xs ih =>
    intro i
    simp only [List.cons_append, mpx, ih (i + 1), List.append_assoc, List.length_cons]
    rw [show i + 1 + xs.length = i + (xs.length + 1) by omega]

/-! ## Lifting a program on the first tapes -/

theorem liftL {m e s W n : ℕ} {P : Machine m s} {σ σ' : Fin m → TS} (h : LRuns W P n σ σ') (x : Fin e → TS) :
    LRuns W (RecoveryFocus.machine (Fin.castAdd e) P) n (Fin.addCases σ x) (Fin.addCases σ' x) := by
  refine h.focus (Fin.castAdd e) (Fin.castAdd_injective m e) _ _ (fun j => by simp) (fun j => by simp) ?_
  intro i hn
  induction i using Fin.addCases with
  | left j => exact absurd rfl (hn j)
  | right j => simp

/-! ## The layout -/

/-- The six extra tapes: output stream and marks, the `j`-stream, three flags. -/
def ex (o : List Bool) (j p : ℕ) (f1 f2 f3 : Bool) : Fin 6 → TS :=
  ![sS o, sM o, .cells (sf (List.replicate (j + 1) true)) p, .flag f1, .flag f2, .flag f3]

/-- The whole role map. -/
def R (w : List Bool) (s : Native.NS) (o : List Bool) (j p : ℕ) (f1 f2 f3 : Bool) : Fin (26 + 6) → TS :=
  Fin.addCases (Native.nv w s) (ex o j p f1 f2 f3)

/-! ## `EmitK`: while `1 < b`, `b := b − 1` and append the bit -/

namespace EmitK

/-- Tapes: 0 ruler, 1 the register `1`, 2 the counter `b`, 3 zero register, 4 flag, 5 stream, 6 marks. -/
def test := swAt subF false false (0 : Fin 7) 1 2 4

def body (x : Bool) :=
  Composition.machine (swAt subF true true (0 : Fin 7) 2 3 4) (RecoveryFocus.machine ![(5 : Fin 7), 6] (sapp x))

def machine (x : Bool) := Loop test (body x) (4 : Fin 7)

def st (o : List Bool) (x : Bool) (B i : ℕ) (b : Bool) : Fin 7 → TS :=
  ![.ruler, .reg 1, .reg (B - i), .reg 0, .flag b, sS (o ++ List.replicate i x), sM (o ++ List.replicate i x)]

theorem test_run (W : ℕ) (o : List Bool) (x : Bool) (B i : ℕ) (b : Bool) (hi : i ≤ B - 1) (hB : B < 2 ^ W)
    (h1 : 1 < 2 ^ W) :
    LRuns W test (2 * W + 3) (st o x B i b) (st o x B i (decide (i < B - 1))) := by
  have h := lt_at (W := W) (st o x B i b) (0 : Fin 7) 1 2 4 (by decide) 1 (B - i) b rfl rfl rfl rfl h1 (by omega)
  refine h.congr_out ?_
  have e : decide (1 < B - i) = decide (i < B - 1) := by
    by_cases h : i < B - 1
    · rw [decide_eq_true h, decide_eq_true (by omega)]
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  rw [e]
  funext j; fin_cases j <;> rfl

theorem body_run (W : ℕ) (o : List Bool) (x : Bool) (B i : ℕ) (hi : i < B - 1) (hB : B < 2 ^ W) :
    LRuns W (body x) (2 * W + 3 + 1 + 1) (st o x B i true) (st o x B (i + 1) false) := by
  have h1 := dec_at (W := W) (st o x B i true) (0 : Fin 7) 2 3 4 (by decide) (B - i) 0 true rfl rfl rfl rfl rfl
    (by omega) (by omega)
  have h2 := (sapp_lruns W x (o ++ List.replicate i x)).dockK ![(5 : Fin 7), 6] (by decide)
    (Function.update (Function.update (st o x B i true) 2 (.reg (B - i - 1))) 4 (.flag false))
    (by intro j; fin_cases j <;> rfl) [0, 1] (by intro j hj; fin_cases j <;> simp at hj)
  refine (h1.seq h2).congr_out ?_
  have e : o ++ List.replicate i x ++ [x] = o ++ List.replicate (i + 1) x := by
    rw [List.replicate_succ', List.append_assoc]
  funext j; fin_cases j
  · rfl
  · rfl
  · exact congrArg TS.reg (by omega)
  · rfl
  · rfl
  · simp only [List.foldr_cons, List.foldr_nil, st]
    rw [e]; rfl
  · simp only [List.foldr_cons, List.foldr_nil, st]
    rw [e]; rfl

def cost (W B : ℕ) : ℕ := (B + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2)

/-- **`b − 1` copies of `x`**, the counter left at `b − (b − 1)` (`0` or `1`). -/
theorem run (W : ℕ) (o : List Bool) (x : Bool) (B : ℕ) (b : Bool) (hB : B < 2 ^ W) (h1 : 1 < 2 ^ W) :
    LRuns W (machine x) (cost W B)
      ![.ruler, .reg 1, .reg B, .reg 0, .flag b, sS o, sM o]
      ![.ruler, .reg 1, .reg (B - (B - 1)), .reg 0, .flag false, sS (o ++ List.replicate (B - 1) x),
        sM (o ++ List.replicate (B - 1) x)] := by
  have h := Loop.runs test (body x) (4 : Fin 7) (fun i => st o x B i (if i = 0 then b else false))
    (fun i => st o x B i (decide (i < B - 1))) (B - 1)
    (fun i hi => test_run W o x B i _ hi hB h1) (fun i _ => rfl)
    (fun i hi => by
      have hb := body_run W o x B i hi hB
      have e1 : decide (i < B - 1) = true := by simp [hi]
      have e2 : (if i + 1 = 0 then b else false) = false := by simp
      rw [e1, e2]
      exact hb)
  refine (lr_src (h.congr_out ?_) ?_).enlarge ?_
  · funext j; fin_cases j
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [st]
    · rfl
    · rfl
  · funext j; fin_cases j <;> simp [st]
  · unfold cost
    exact Nat.mul_le_mul_right _ (by omega)

end EmitK

/-! ## The per-block pieces on the 32 tapes -/

/-- Emit `b − 1` copies of `x` (ruler 4, the register `k = 1` at 17, `b` at 13, zero at 7, flag 31, stream 26/27). -/
def emitM (x : Bool) := RecoveryFocus.machine ![(4 : Fin (26 + 6)), 17, 13, 7, 31, 26, 27] (EmitK.machine x)

theorem R_eq_upd_b (w : List Bool) (s : Native.NS) (o : List Bool) (j p : ℕ) (f1 f2 f3 : Bool) (v : ℕ) (o' : List Bool)
    (f3' : Bool) (hk : s.k = 1) :
    (([0, 1, 2, 3, 4, 5, 6] : List (Fin 7)).foldr (fun k ρ => Function.update ρ
      ((![(4 : Fin (26 + 6)), 17, 13, 7, 31, 26, 27] : Fin 7 → Fin (26 + 6)) k)
      ((![.ruler, .reg 1, .reg v, .reg 0, .flag f3', sS o', sM o'] : Fin 7 → TS) k)) (R w s o j p f1 f2 f3)) =
      R w { s with b := v } o' j p f1 f2 f3' := by
  funext i
  fin_cases i <;> first | rfl | exact congrArg TS.reg hk.symm

theorem emitM_run (W : ℕ) (w : List Bool) (s : Native.NS) (o : List Bool) (j p : ℕ) (f1 f2 f3 : Bool) (x : Bool)
    (B : ℕ) (hsb : s.b = B) (hk : s.k = 1) (hB : B < 2 ^ W) (h1 : 1 < 2 ^ W) :
    LRuns W (emitM x) (EmitK.cost W B) (R w s o j p f1 f2 f3)
      (R w { s with b := B - (B - 1) } (o ++ List.replicate (B - 1) x) j p f1 f2 false) := by
  have h := (EmitK.run W o x B f3 hB h1).dockK ![(4 : Fin (26 + 6)), 17, 13, 7, 31, 26, 27] (by decide)
    (R w s o j p f1 f2 f3)
    (by
      intro i; fin_cases i
      · rfl
      · exact congrArg TS.reg hk
      · exact congrArg TS.reg hsb
      · rfl
      · rfl
      · rfl
      · rfl) [0, 1, 2, 3, 4, 5, 6] (by intro i hi; fin_cases i <;> simp at hi)
  rw [R_eq_upd_b w s o j p f1 f2 f3 _ _ _ hk] at h
  exact h

/-- Peek the `j`-stream into flag `f` (29 or 30). -/
def peekJ (f : Fin (26 + 6)) := RecoveryFocus.machine ![(28 : Fin (26 + 6)), f] peek

theorem peek1_run (W : ℕ) (w : List Bool) (s : Native.NS) (o : List Bool) (j p : ℕ) (f1 f2 f3 : Bool) :
    LRuns W (peekJ 29) 1 (R w s o j p f1 f2 f3)
      (R w s o j p (sf (List.replicate (j + 1) true) p) f2 f3) := by
  have h := (peek_lruns W p (sf (List.replicate (j + 1) true)) f1).dockK ![(28 : Fin (26 + 6)), 29] (by decide)
    (R w s o j p f1 f2 f3) (by intro i; fin_cases i <;> rfl) [0, 1] (by intro i hi; fin_cases i <;> simp at hi)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

theorem peek2_run (W : ℕ) (w : List Bool) (s : Native.NS) (o : List Bool) (j p : ℕ) (f1 f2 f3 : Bool) :
    LRuns W (peekJ 30) 1 (R w s o j p f1 f2 f3)
      (R w s o j p f1 (sf (List.replicate (j + 1) true) p) f3) := by
  have h := (peek_lruns W p (sf (List.replicate (j + 1) true)) f2).dockK ![(28 : Fin (26 + 6)), 30] (by decide)
    (R w s o j p f1 f2 f3) (by intro i; fin_cases i <;> rfl) [0, 1] (by intro i hi; fin_cases i <;> simp at hi)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

def moveJ := RecoveryFocus.machine ![(28 : Fin (26 + 6))] moveR

theorem moveJ_run (W : ℕ) (w : List Bool) (s : Native.NS) (o : List Bool) (j p : ℕ) (f1 f2 f3 : Bool) :
    LRuns W moveJ 1 (R w s o j p f1 f2 f3) (R w s o j (p + 1) f1 f2 f3) := by
  have h := (moveR_lruns W p (sf (List.replicate (j + 1) true))).dockK ![(28 : Fin (26 + 6))] (by decide)
    (R w s o j p f1 f2 f3) (by intro i; fin_cases i; rfl) [0] (by intro i hi; fin_cases i; simp at hi)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- Choose the bit `decide (c = j)` from the two peeks and emit. -/
def emitSel := Ite (peekJ 30) (emitM false) (Ite (nop (26 + 6)) (emitM true) (emitM false) (29 : Fin (26 + 6)))
  (30 : Fin (26 + 6))

def emitSelCost (W B : ℕ) : ℕ := 1 + EmitK.cost W B + (0 + EmitK.cost W B + EmitK.cost W B + 2) + 2

theorem sf_rep1 (j c : ℕ) : sf (List.replicate (j + 1) true) (1 + c) = decide (c ≤ j) := by
  rw [sf_rep]
  by_cases h : c ≤ j
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

theorem sf_rep2 (j c : ℕ) : sf (List.replicate (j + 1) true) (2 + c) = decide (c < j) := by
  rw [sf_rep]
  by_cases h : c < j
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

/-- **The bit `decide (c = j)`, emitted `b − 1` times.** -/
theorem emitSel_run (W : ℕ) (w : List Bool) (s : Native.NS) (o : List Bool) (j c : ℕ) (f2 f3 : Bool)
    (B : ℕ) (hsb : s.b = B) (hk : s.k = 1) (hB : B < 2 ^ W) (h1 : 1 < 2 ^ W) :
    LRuns W emitSel (emitSelCost W B)
      (R w s o j (2 + c) (sf (List.replicate (j + 1) true) (1 + c)) f2 f3)
      (R w { s with b := B - (B - 1) } (o ++ List.replicate (B - 1) (decide (c = j))) j (2 + c)
        (sf (List.replicate (j + 1) true) (1 + c)) (sf (List.replicate (j + 1) true) (2 + c)) false) := by
  unfold emitSel emitSelCost
  refine Ite.runs (W := W) _ _ _ (30 : Fin (26 + 6)) (sf (List.replicate (j + 1) true) (2 + c))
    (peek2_run W w s o j (2 + c) _ f2 f3) rfl ?_ ?_
  · intro hb
    have hlt : c < j := by rw [sf_rep2] at hb; simpa using hb
    have e : decide (c = j) = false := decide_eq_false (by omega)
    rw [e]
    exact emitM_run W w s o j (2 + c) _ _ _ false B hsb hk hB h1
  · intro _
    refine Ite.runs (W := W) _ _ _ (29 : Fin (26 + 6)) (sf (List.replicate (j + 1) true) (1 + c))
      (nop_lruns _) rfl ?_ ?_
    · intro hb1
      have hle : c ≤ j := by rw [sf_rep1] at hb1; simpa using hb1
      have hnlt : ¬ c < j := by
        intro h
        have := ‹sf (List.replicate (j + 1) true) (2 + c) = false›
        rw [sf_rep2] at this
        simp [h] at this
      have e : decide (c = j) = true := decide_eq_true (by omega)
      rw [e]
      exact emitM_run W w s o j (2 + c) _ _ _ true B hsb hk hB h1
    · intro hb1
      have hgt : ¬ c ≤ j := by rw [sf_rep1] at hb1; simpa using hb1
      have e : decide (c = j) = false := decide_eq_false (by omega)
      rw [e]
      exact emitM_run W w s o j (2 + c) _ _ _ false B hsb hk hB h1

/-! ## One block -/

/-- PK's circuit block `c` on the first 26 tapes, then the two peeks and the emission. -/
def myBlock (c : Fin 4) :=
  Composition.machine (RecoveryFocus.machine (Fin.castAdd 6) (Native.block c))
    (Composition.machine (peekJ 29) (Composition.machine moveJ emitSel))

def myBlockCost (W m : ℕ) : ℕ := Native.blockCost W m + 1 + (1 + 1 + (1 + 1 + emitSelCost W (m + 1)))

theorem emitSelCost_mono (W B B' : ℕ) (h : B ≤ B') : emitSelCost W B ≤ emitSelCost W B' := by
  unfold emitSelCost EmitK.cost
  have := Nat.mul_le_mul_right ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2) (show B + 1 ≤ B' + 1 by omega)
  omega

/-- The block tail: peek, move, emit. -/
theorem tail_run (W : ℕ) (w : List Bool) (s : Native.NS) (o : List Bool) (j c : ℕ) (f1 f2 f3 : Bool)
    (B : ℕ) (hsb : s.b = B) (hk : s.k = 1) (hB : B < 2 ^ W) (h1 : 1 < 2 ^ W) :
    LRuns W (Composition.machine (peekJ 29) (Composition.machine moveJ emitSel)) (1 + 1 + (1 + 1 + emitSelCost W B))
      (R w s o j (1 + c) f1 f2 f3)
      (R w { s with b := B - (B - 1) } (o ++ List.replicate (B - 1) (decide (c = j))) j (2 + c)
        (sf (List.replicate (j + 1) true) (1 + c)) (sf (List.replicate (j + 1) true) (2 + c)) false) := by
  have e1 := peek1_run W w s o j (1 + c) f1 f2 f3
  have e2 := moveJ_run W w s o j (1 + c) (sf (List.replicate (j + 1) true) (1 + c)) f2 f3
  rw [show 1 + c + 1 = 2 + c by omega] at e2
  have e3 := emitSel_run W w s o j c f2 f3 B hsb hk hB h1
  exact e1.seq (e2.seq e3)

/-- The chain state of the mask program after `c` blocks. -/
def mst {α : Type} (w : List Bool) (S0 : Native.NS) (pre : List Bool) (L : List α) (pay : α → List Bool)
    (num : α → ℕ) (j c bb pp : ℕ) (f1 f2 f3 : Bool) : Fin (26 + 6) → TS :=
  R w (Native.chainSt S0 pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) c bb pp)
    (mpx ((L.map num).take c) j 0) j (1 + c) f1 f2 f3

/-- **One block of the mask program.** -/
theorem block_run {α : Type} {W : ℕ} (w pre : List Bool) (L : List α) (pay : α → List Bool) (num : α → ℕ)
    (hw : w = pre ++ L.flatMap (fun a => RepairOrdinary.frame (pay a)))
    (hpay : ∀ a, ∃ rest, pay a = natWord (num a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ W) (hW1 : 1 ≤ W)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ W) (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ W)
    (hsumLe : (L.map (fun a => num a + 1)).sum ≤ w.length)
    (S0 : Native.NS) (hk : S0.k = 1) (j : ℕ) (c : Fin 4) (bb pp : ℕ) (hbb : bb ≤ 1) (f1 f2 f3 : Bool) :
    ∃ bb' pp', bb' ≤ 1 ∧ LRuns W (myBlock c) (myBlockCost W w.length)
      (mst w S0 pre L pay num j c.val bb pp f1 f2 f3)
      (mst w S0 pre L pay num j (c.val + 1) bb' pp' (sf (List.replicate (j + 1) true) (1 + c.val))
        (sf (List.replicate (j + 1) true) (2 + c.val)) false) := by
  set F : α → List Bool := fun a => RepairOrdinary.frame (pay a) with hF
  set g : α → ℕ := fun a => num a + 1 with hg
  have h2 : 1 < 2 ^ W := by
    have : 2 ^ 1 ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW1
    omega
  by_cases hc : c.val < L.length
  · -- a circuit is present
    obtain ⟨rest, hr⟩ := hpay L[c.val]
    have hsplit := Native.flatMap_split L F c.val hc
    have hpl : (pay L[c.val]).length ≤ w.length := by
      have h1 : (F L[c.val]).length ≤ w.length := by
        rw [hw, hsplit]; simp only [List.length_append]; omega
      have h2 : (F L[c.val]).length = 2 * (pay L[c.val]).length + 1 := RepairOrdinary.frame_length _
      omega
    have hX : ∀ i, i < (RepairOrdinary.frame (pay L[c.val])).length →
        sf w ((Native.chainSt S0 pre L F g c.val bb pp).sp + i) =
          (RepairOrdinary.frame (pay L[c.val])).getD i false := by
      intro i hi
      have e : w = (pre ++ (L.take c.val).flatMap F) ++ F L[c.val] ++ (L.drop (c.val + 1)).flatMap F := by
        rw [hw, hsplit]; simp only [List.append_assoc]
      have := Native.sf_mid (pre ++ (L.take c.val).flatMap F) (F L[c.val]) ((L.drop (c.val + 1)).flatMap F) i hi
      rw [e]
      convert this using 2
      simp only [Native.chainSt, List.length_append]
      omega
    have hsum1 := Native.sum_take_le L g (c.val + 1)
    have hprod1 := Native.prod_take_le L g (fun a _ => by simp [hg]) (c.val + 1)
    rw [Native.take_succ_of_lt L c.val hc, List.map_append, List.sum_append] at hsum1
    rw [Native.take_succ_of_lt L c.val hc, List.map_append, List.prod_append] at hprod1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil,
      Nat.add_zero, Nat.mul_one] at hsum1 hprod1
    have hx : num L[c.val] + 1 < 2 ^ W := by
      show g L[c.val] < 2 ^ W
      have := lt_of_le_of_lt hsum1 hsumB
      omega
    have hxle : num L[c.val] + 1 ≤ w.length := by
      have h3 : g L[c.val] ≤ (L.map g).sum := by
        have := hsum1
        have h4 := Native.sum_take_le L g (c.val + 1)
        omega
      show g L[c.val] ≤ w.length
      omega
    have hb := Native.block_present (W := W) w (Native.chainSt S0 pre L F g c.val bb pp) c (pay L[c.val]) rest
      (num L[c.val]) hr hX rfl (hnb _ (List.getElem_mem hc)) hW1 hx (by
        show ((L.take c.val).map g).sum + g L[c.val] < 2 ^ W
        exact lt_of_le_of_lt hsum1 hsumB)
      (by
        show ((L.take c.val).map g).prod * g L[c.val] < 2 ^ W
        exact lt_of_le_of_lt hprod1 hprodB)
    have hstate : ({ Native.bodyOut (Native.chainSt S0 pre L F g c.val bb pp) c (pay L[c.val]) (num L[c.val]) with
        ct := Native.ctAfter (c.val + 1) } : Native.NS) =
        Native.chainSt S0 pre L F g (c.val + 1) (num L[c.val] + 1)
          (((L.take c.val).map g).prod * (num L[c.val] + 1)) := by
      simp only [Native.bodyOut, Native.rbS, Native.uf, Native.chainSt, Native.take_succ_of_lt L c.val hc,
        List.flatMap_append, List.map_append, List.sum_append, List.prod_append, List.length_append,
        List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.prod_cons, List.prod_nil, List.append_nil]
      simp only [hF, hg]
      congr 1 <;> ring
    rw [hstate] at hb
    have hl := liftL hb (ex (mpx ((L.map num).take c.val) j 0) j (1 + c.val) f1 f2 f3)
    have ht := tail_run W w (Native.chainSt S0 pre L F g (c.val + 1) (num L[c.val] + 1)
      (((L.take c.val).map g).prod * (num L[c.val] + 1))) (mpx ((L.map num).take c.val) j 0) j c.val f1 f2 f3
      (num L[c.val] + 1) rfl hk hx h2
    refine ⟨1, ((L.take c.val).map g).prod * (num L[c.val] + 1), le_rfl, ?_⟩
    have hall := (hl.seq ht).enlarge (m := myBlockCost W w.length) (by
      unfold myBlockCost
      have := emitSelCost_mono W (num L[c.val] + 1) (w.length + 1) (by omega)
      show Native.blockCost W (pay L[c.val]).length + 1 + (1 + 1 + (1 + 1 + emitSelCost W (num L[c.val] + 1))) ≤ _
      have hbc : Native.blockCost W (pay L[c.val]).length ≤ Native.blockCost W w.length := by
        unfold Native.blockCost Native.bodyCost; omega
      omega)
    refine hall.congr_out ?_
    have hm : mpx ((L.map num).take c.val) j 0 ++ List.replicate (num L[c.val] + 1 - 1) (decide (c.val = j)) =
        mpx ((L.map num).take (c.val + 1)) j 0 := by
      have hc' : c.val < (L.map num).length := by simpa using hc
      rw [List.take_succ_eq_append_getElem hc', mpx_snoc]
      have hlen : ((L.map num).take c.val).length = c.val := by simp; omega
      rw [hlen, Nat.zero_add, Nat.add_sub_cancel]
      simp only [List.getElem_map]
    unfold mst
    rw [← hm, show 1 + (c.val + 1) = 2 + c.val by omega,
      show num L[c.val] + 1 - (num L[c.val] + 1 - 1) = 1 by omega]
    rfl
  · -- no circuit left
    have hle : L.length ≤ c.val := by omega
    have htake : L.take c.val = L := List.take_of_length_le hle
    have htake1 : L.take (c.val + 1) = L := List.take_of_length_le (by omega)
    have hbit : sf w (Native.chainSt S0 pre L F g c.val bb pp).sp = false := by
      simp only [Native.chainSt, htake]
      rw [show 1 + pre.length + (L.flatMap F).length = (pre.length + (L.flatMap F).length) + 1 by omega, sf_succ]
      apply List.getD_eq_default
      rw [hw]; simp
    have hb := Native.block_absent (W := W) w (Native.chainSt S0 pre L F g c.val bb pp) c w.length hbit rfl
    have hstate : ({ Native.chainSt S0 pre L F g c.val bb pp with fl := false, ct := Native.ctAfter (c.val + 1) } :
        Native.NS) = Native.chainSt S0 pre L F g (c.val + 1) bb pp := by
      simp only [Native.chainSt, htake, htake1]
    rw [hstate] at hb
    have hl := liftL hb (ex (mpx ((L.map num).take c.val) j 0) j (1 + c.val) f1 f2 f3)
    have hbW : bb < 2 ^ W := by omega
    have ht := tail_run W w (Native.chainSt S0 pre L F g (c.val + 1) bb pp) (mpx ((L.map num).take c.val) j 0) j
      c.val f1 f2 f3 bb rfl hk hbW h2
    refine ⟨bb, pp, hbb, ?_⟩
    have hall := (hl.seq ht).enlarge (m := myBlockCost W w.length) (by
      unfold myBlockCost
      have := emitSelCost_mono W bb (w.length + 1) (by omega)
      show Native.blockCost W w.length + 1 + (1 + 1 + (1 + 1 + emitSelCost W bb)) ≤ _
      omega)
    refine hall.congr_out ?_
    have hmt : (L.map num).take (c.val + 1) = (L.map num).take c.val := by
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
    have hbb' : bb - (bb - 1) = bb := by omega
    have hrep : List.replicate (bb - 1) (decide (c.val = j)) = [] := by
      rw [show bb - 1 = 0 by omega]; rfl
    unfold mst
    rw [hbb', hrep, List.append_nil, hmt, show 1 + (c.val + 1) = 2 + c.val by omega]
    rfl

/-! ## The whole program -/

theorem mpx_length (bs : List ℕ) (j : ℕ) : ∀ i, (mpx bs j i).length = bs.sum := by
  induction bs with
  | nil => intro i; rfl
  | cons b bs ih => intro i; simp [mpx, ih]

theorem sum_map_le {α : Type} (L : List α) (f g : α → ℕ) (h : ∀ a, f a ≤ g a) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; have := h a; omega

theorem sf_nil : sf [] = blank := by
  funext j; cases j <;> rfl

/-- The entry roles of the six extra tapes: blank output pair, the `j`-stream at cursor `1`, three flags. -/
def exIn (j : ℕ) : Fin 6 → TS :=
  ![.cells blank 0, .cells blank 0, .cells (sf (List.replicate (j + 1) true)) 1, .flag false, .flag false, .flag false]

/-- Both output tapes to cursor `1`. -/
def initOut := RecoveryFocus.machine ![(26 : Fin (26 + 6)), 27] (oneStep 2 (fun _ => (fun _ => none, fun _ => .right)))

theorem initOut_local (W : ℕ) :
    LRuns W (oneStep 2 (fun _ => (fun _ => none, fun _ => .right))) 1 ![.cells blank 0, .cells blank 0]
      ![sS [], sM []] := by
  intro H A hA
  have h0 : H 0 = 0 ∧ ∀ j, readTapeBit (A 0) j = blank j := hA 0
  have h1 : H 1 = 0 ∧ ∀ j, readTapeBit (A 1) j = blank j := hA 1
  refine ⟨_, _, oneStep_run 2 _ H A, ?_⟩
  intro i
  fin_cases i
  · refine ⟨by simp [HeadMove.apply, h0.1], fun j => ?_⟩
    simp only [acted]
    rw [sf_nil]; exact h0.2 j
  · refine ⟨by simp [HeadMove.apply, h1.1], fun j => ?_⟩
    simp only [acted]
    rw [List.length_nil, List.replicate_zero, sf_nil]; exact h1.2 j

theorem initOut_run (W : ℕ) (σ : Fin 26 → TS) (j : ℕ) :
    LRuns W initOut 1 (Fin.addCases σ (exIn j)) (Fin.addCases σ (ex [] j 1 false false false)) := by
  have h := (initOut_local W).dockK ![(26 : Fin (26 + 6)), 27] (by decide) (Fin.addCases σ (exIn j))
    (by intro i; fin_cases i <;> rfl) [0, 1] (by intro i hi; fin_cases i <;> simp at hi)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- Rewind the output pair to cursor `1`. -/
def rewindOut := RecoveryFocus.machine ![(27 : Fin (26 + 6)), 26] rewind

/-- The program's first 26 tapes, lifted. -/
abbrev liftM {s : ℕ} (P : Machine 26 s) := RecoveryFocus.machine (Fin.castAdd 6) P

/-- **The SYM mask-bit program.** -/
def maskProg :=
  Composition.machine initOut
    (Composition.machine (liftM Native.front)
      (Composition.machine (liftM Native.header)
        (Composition.machine (liftM (swAt addF true true (4 : Fin 26) 12 7 6))
          (Composition.machine (myBlock 0)
            (Composition.machine (myBlock 1)
              (Composition.machine (myBlock 2)
                (Composition.machine (myBlock 3) rewindOut)))))))

def maskCost (W m : ℕ) : ℕ :=
  1 + 1 + (Native.frontCost W m + 1 + (Native.headerCost W + 1 + ((2 * W + 3) + 1 +
    (myBlockCost W m + 1 + (myBlockCost W m + 1 + (myBlockCost W m + 1 + (myBlockCost W m + 1 + (m + 5))))))))

theorem start_eq {α : Type} (S : Native.NS) (pre : List Bool) (L : List α) (F : α → List Bool) (g : α → ℕ)
    (hsp : S.sp = 1 + pre.length) (hsum : S.sum = 0) (hprod : S.prod = 0) (hct : S.ct = Native.ctAfter 0) :
    ({ S with prod := S.prod + 1, fl := false } : Native.NS) = Native.chainSt S pre L F g 0 S.b S.p2 := by
  cases S
  simp only [Native.chainSt] at hsp hsum hprod hct ⊢
  subst hsp hsum hprod hct
  simp

/-- **The mask program's run.** On the native word of a SYM request (`hdr 0 … ++ circuits.flatMap (frame ∘ pay)`),
with the `j`-stream on tape 28, the output pair ends holding `mpx (L.map num) j 0` at cursor `1`. -/
theorem maskProg_run {α : Type} (q Lv tg : ℕ) (L : List α) (pay : α → List Bool) (num : α → ℕ) (j : ℕ)
    (w : List Bool) (hw : w = Native.hdr 0 q Lv tg L.length ++ L.flatMap (fun a => RepairOrdinary.frame (pay a)))
    (hpay : ∀ a, ∃ rest, pay a = natWord (num a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ 8 * w.length)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ (8 * w.length))
    (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ (8 * w.length))
    (hsumLe : (L.map (fun a => num a + 1)).sum ≤ w.length) (hL : L.length ≤ 4) :
    ∃ σ' : Fin (26 + 6) → TS, LRuns (8 * w.length) maskProg (maskCost (8 * w.length) w.length)
      (Fin.addCases (PacketsKeys.initRoles 26 w) (exIn j)) σ' ∧
      σ' 26 = .cells (sf (mpx (L.map num) j 0)) 1 ∧
      σ' 27 = .cells (sf (List.replicate (mpx (L.map num) j 0).length true)) 1 := by
  have hW1 : 1 ≤ w.length := by rw [hw]; simp [Native.hdr, ReadNat.natWord_length]; omega
  have hW8 : 1 ≤ 8 * w.length := by omega
  have hwl : w.length < 2 ^ (8 * w.length) := PacketsKeys.Native.small_lt _ hW1
  have e0 := initOut_run (8 * w.length) (PacketsKeys.initRoles 26 w) j
  have e1 := liftL (Native.front_run w (natWord q ++ natWord Lv ++ natWord tg ++ natWord L.length ++
    L.flatMap (fun a => RepairOrdinary.frame (pay a))) 0 (by rw [hw]; simp [Native.hdr]) (by omega) hW1)
    (ex [] j 1 false false false)
  have e2 := liftL (Native.header_run w (L.flatMap (fun a => RepairOrdinary.frame (pay a))) 0 q Lv tg L.length hw
    (by omega)) (ex [] j 1 false false false)
  have e3 := liftL (Native.incProd (W := 8 * w.length) w (Native.sH w 0 q Lv tg L.length) (by
    show 0 + 1 < _
    omega)) (ex [] j 1 false false false)
  have hs0 := start_eq (Native.sH w 0 q Lv tg L.length) (Native.hdr 0 q Lv tg L.length) L
    (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) rfl rfl rfl rfl
  rw [hs0] at e3
  have hk : (Native.sH w 0 q Lv tg L.length).k = 1 := rfl
  obtain ⟨b1, p1, hb1, g0⟩ := block_run (W := 8 * w.length) w (Native.hdr 0 q Lv tg L.length) L pay num hw hpay hnb hW8 hsumB hprodB hsumLe
    (Native.sH w 0 q Lv tg L.length) hk j 0 0 0 (Nat.zero_le 1) false false false
  obtain ⟨b2, p2, hb2, g1⟩ := block_run (W := 8 * w.length) w (Native.hdr 0 q Lv tg L.length) L pay num hw hpay hnb hW8 hsumB hprodB hsumLe
    (Native.sH w 0 q Lv tg L.length) hk j 1 b1 p1 hb1 _ _ _
  obtain ⟨b3, p3, hb3, g2⟩ := block_run (W := 8 * w.length) w (Native.hdr 0 q Lv tg L.length) L pay num hw hpay hnb hW8 hsumB hprodB hsumLe
    (Native.sH w 0 q Lv tg L.length) hk j 2 b2 p2 hb2 _ _ _
  obtain ⟨b4, p4, hb4, g3⟩ := block_run (W := 8 * w.length) w (Native.hdr 0 q Lv tg L.length) L pay num hw hpay hnb hW8 hsumB hprodB hsumLe
    (Native.sH w 0 q Lv tg L.length) hk j 3 b3 p3 hb3 _ _ _
  set m := mpx (L.map num) j 0 with hm
  have htake : (L.map num).take 4 = L.map num := List.take_of_length_le (by simp; omega)
  have hml : m.length ≤ w.length := by
    rw [hm, mpx_length]
    have h := sum_map_le L num (fun a => num a + 1) (fun a => by omega)
    omega
  have e5 := (rewind_lruns (8 * w.length) m.length (m.length + 1) (sf m) (by omega) (by omega)).dockK
    ![(27 : Fin (26 + 6)), 26] (by decide)
    (mst w (Native.sH w 0 q Lv tg L.length) (Native.hdr 0 q Lv tg L.length) L pay num j 4 b4 p4 (sf (List.replicate (j + 1) true) (1 + 3))
      (sf (List.replicate (j + 1) true) (2 + 3)) false)
    (by intro i; fin_cases i <;> (simp only [mst, htake]; rfl)) [0, 1] (by intro i hi; fin_cases i <;> simp at hi)
  have hall := e0.seq (e1.seq (e2.seq (e3.seq (g0.seq (g1.seq (g2.seq (g3.seq e5)))))))
  refine ⟨_, hall.enlarge ?_, rfl, rfl⟩
  unfold maskCost
  omega

end
end NearCubicWires.PacketsSymBits

