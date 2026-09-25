import Proof.Packets.PacketsCursorFlags
import Proof.Packets.PacketsKeysStageOn
import Proof.Packets.PacketsLowerAdapter
import Proof.Packets.PacketsSymBitsProg

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsSymBits.Meta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsMeta
open NearCubicWires.PacketsSymBits.Win
noncomputable section

/-! ## The lookup bits as windows of the top tables -/

theorem sf_ofFn_succ {m : ℕ} (f : Fin m → Bool) (x : ℕ) :
    sf (List.ofFn f) (x + 1) = if h : x < m then f ⟨x, h⟩ else false := by
  rw [sf_succ]
  by_cases h : x < m
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa using h)]

theorem bc_le_pop (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (i : Fin r.circuits.length) :
    (r.circuits.get i).bottomCount ≤ (symmetricFourfoldOccurrences r).length := by
  rw [← symmetricCircuitMask_card r i]
  simpa using Finset.card_le_card (Finset.subset_univ (symmetricCircuitMask r i))

/-- **Block `i` of the lookup bits is a window of circuit `i`'s top table.** -/
theorem win_top (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (i : Fin r.circuits.length) (off : ℕ) :
    win (List.ofFn (r.circuits.get i).top) off ((symmetricFourfoldOccurrences r).length + 1) =
      List.ofFn (shiftedFiniteLookup (population := (symmetricFourfoldOccurrences r).length) off
        (symmetricCircuitTopLookup r i)) := by
  have hb := bc_le_pop r i
  unfold win
  congr 1
  funext t
  rw [show 1 + off + t.val = (off + t.val) + 1 by omega, sf_ofFn_succ]
  unfold shiftedFiniteLookup symmetricCircuitTopLookup
  by_cases h1 : off + t.val < (r.circuits.get i).bottomCount + 1
  · rw [dif_pos h1, dif_pos (show off + t.val < (symmetricFourfoldOccurrences r).length + 1 by omega)]
    simp only
    rw [dif_pos h1]
  · rw [dif_neg h1]
    split_ifs <;> rfl

theorem outAt_ofFn {α : Type} (L : List α) (tp : α → List Bool) (offs : ℕ → ℕ) (P : ℕ) :
    ∀ c, Prog.outAt L tp offs P c = (List.ofFn (fun i : Fin c => Prog.winAt L tp offs P i.val)).flatten := by
  intro c
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Prog.outAt_succ, ih, List.ofFn_succ_last, List.flatten_append]
    simp

theorem outAt_past {α : Type} (L : List α) (tp : α → List Bool) (offs : ℕ → ℕ) (P : ℕ) :
    ∀ e, Prog.outAt L tp offs P (L.length + e) = Prog.outAt L tp offs P L.length := by
  intro e
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [← Nat.add_assoc, Prog.outAt_succ, ih]
    simp [Prog.winAt]

/-- The unary offset of key field `d` (`0` past the eight fields). -/
def offsOf (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) (d : ℕ) : ℕ :=
  if h : d < 8 then keyDigits a r (some k) ⟨d, h⟩ else 0

theorem offsOf_sym (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) (i : Fin r.circuits.length) :
    offsOf a (.sym r four L target) k i.val = k.offset i := by
  have hi := i.isLt
  unfold offsOf
  rw [dif_pos (by omega)]
  show (if h : i.val < r.circuits.length then k.offset ⟨i.val, h⟩
    else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val else 0) = _
  rw [dif_pos hi]

/-- **The program's output is the lookup-bit word.** -/
theorem symBits_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) :
    Prog.outAt r.circuits (fun c => List.ofFn c.top) (offsOf a (.sym r four L target) k)
      ((symmetricFourfoldOccurrences r).length + 1) 4 = PacketsCombine.symBitsWord r L target k := by
  rw [show (4 : ℕ) = r.circuits.length + (4 - r.circuits.length) by omega, outAt_past, outAt_ofFn]
  unfold PacketsCombine.symBitsWord
  congr 1
  congr 1
  funext i
  unfold Prog.winAt
  rw [dif_pos i.isLt, offsOf_sym a r four L target k i, ← win_top r i]
  rfl

theorem symBits_length (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : ℕ)
    (k : RCFive.RowKeys.SymKey r L target) :
    (PacketsCombine.symBitsWord r L target k).length =
      r.circuits.length * ((symmetricFourfoldOccurrences r).length + 1) := by
  unfold PacketsCombine.symBitsWord
  simp [List.length_flatten, List.sum_ofFn]

/-! ## Key bounds -/

theorem offset_le (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : ℕ)
    (k : RCFive.RowKeys.SymKey r L target) (hk : k ∈ RCFive.RowKeys.symKeys r L target) (i : Fin r.circuits.length) :
    k.offset i ≤ (r.circuits.get i).bottomCount := by
  unfold RCFive.RowKeys.symKeys at hk
  rw [List.mem_flatMap] at hk
  obtain ⟨seed, _, hk⟩ := hk
  rw [List.mem_map] at hk
  obtain ⟨offset, ho, rfl⟩ := hk
  unfold Packets.symOffsetList at ho
  rw [List.mem_map] at ho
  obtain ⟨o, _, rfl⟩ := ho
  have := (o i).isLt
  simp only at this ⊢
  omega

/-! ## The fifteen key-level words -/

section Words
variable (a : DecompositionAlgorithm)

def mS : UnaryStage a (fun r => pop a r + 1) := (popStage a).thenMapP (plusMap 1) 6 1 (plus_cost 1)

def nmS : UnaryStage a (fun r => PacketsKeys.Native.nCirc r * (pop a r + 1)) :=
  (PacketsKeys.Native.circuitsStage a).pairP (mS a) mulMap2 8 2 mul_cost

/-- The words on the vector's tapes `9 + j`. -/
def symOuts (j : ℕ) (r : Request) (k : rcKey a r) : List Bool :=
  if j < 2 then UnaryTemplate.tape (kitC a r)
  else if j = 2 then UnaryTemplate.tape (wOf a r) else if j = 3 then UnaryTemplate.tape (pop a r + 1)
  else if j = 4 then UnaryTemplate.tape (PacketsKeys.Native.nCirc r)
  else if j = 5 then UnaryTemplate.tape (PacketsKeys.Native.nCirc r * (pop a r + 1))
  else if j = 6 then RepairOrdinary.frame (fields a r 0)
  else if j < 11 then List.replicate (offsOf a r k (j - 7)) true else List.replicate (pop a r + 1) true

/-- Transport a key-level word along a pointwise equality of its values. -/
def kwCongr {v w : ∀ r : Request, rcKey a r → List Bool} (s : KeyWord a v) (h : ∀ r k, v r k = w r k) :
    KeyWord a w where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  costC := s.costC
  costD := s.costD
  cost_le := s.cost_le
  run := fun r k hk => (s.run r k hk).elim fun H e => e.elim fun A f =>
    ⟨H, A, f.1, f.2.1, f.2.2.1.trans (h r k), f.2.2.2⟩

def fk (d : ℕ) (hd : d < 8) : KeyWord a (fun r k => List.replicate (offsOf a r k d) true) :=
  kwCongr a (NearCubicWires.PacketsMeta.Keys.fieldKey a ⟨d, hd⟩) (fun r k => by rw [offsOf, dif_pos hd])

def symVec0 (wS : UnaryStage a (wOf a)) :=
  (((((((((((((((Cursor.KeyVec.nil a (symOuts a)).snoc (KeyWord.ofWord (kitCStage a).tplP)).snoc
    (KeyWord.ofWord (kitCStage a).tplP)).snoc (KeyWord.ofWord wS.tplP)).snoc (KeyWord.ofWord (mS a).tplP)).snoc
    (KeyWord.ofWord (PacketsKeys.Native.circuitsStage a).tplP)).snoc (KeyWord.ofWord (nmS a).tplP)).snoc
    (KeyWord.ofWord (PacketsKeys.Stage.fieldFrame a 0))).snoc (fk a 0 (by omega))).snoc (fk a 1 (by omega))).snoc
    (fk a 2 (by omega))).snoc (fk a 3 (by omega))).snoc (KeyWord.ofWord (mS a).toWord)).snoc
    (KeyWord.ofWord (mS a).toWord)).snoc (KeyWord.ofWord (mS a).toWord)).snoc (KeyWord.ofWord (mS a).toWord)

/-- **The fifteen words, one fixed machine.** -/
def symVec (wS : UnaryStage a (wOf a)) : Cursor.KeyVec a 15 (symOuts a) :=
  (symVec0 a wS).congr (by intro j hj r k; interval_cases j <;> rfl)

end Words

theorem symOuts_off (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) (d : ℕ) (hd : d < 4) :
    symOuts a (7 + d) r k = List.replicate (offsOf a r k d) true := by
  unfold symOuts
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega), show 7 + d - 7 = d by omega]

theorem symOuts_len (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) (d : ℕ) (hd : d < 4) :
    symOuts a (11 + d) r k = List.replicate (pop a r + 1) true := by
  unfold symOuts
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

/-! ## The slot maps -/

/-- The vector: tapes `0..14` stay (key fields, six templates), the frame word to the program's tape 0 (`16`), the
offsets and window lengths to the program's tapes `36..43` (`52..59`), private tapes past the program (`62..`). -/
def vsV (i : ℕ) : ℕ := if i < 15 then i else if i = 15 then 16 else if i < 24 then 36 + i else 38 + i

def vs (e : ℕ) (i : Fin (9 + 15 + e)) : Fin (16 + (46 + e)) := ⟨vsV i.val, by unfold vsV; split_ifs <;> omega⟩

theorem vs_val (e : ℕ) (i : Fin (9 + 15 + e)) : (vs e i).val = vsV i.val := rfl

theorem vs_inj (e : ℕ) : Function.Injective (vs e) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [vs_val, vs_val] at hv
  unfold vsV at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The program: its tape `j` at `16 + j`. -/
def ps (e : ℕ) (j : Fin (26 + 20)) : Fin (16 + (46 + e)) := ⟨16 + j.val, by omega⟩

theorem ps_inj (e : ℕ) : Function.Injective (ps e) := by
  intro x y h
  have hv := congrArg Fin.val h
  simp only [ps] at hv
  exact Fin.ext (by omega)

/-- The exact copy: the program's output stream and marks (`42`, `43`) onto tape 15. -/
def es (e : ℕ) : Fin 3 → Fin (16 + (46 + e)) := ![⟨42, by omega⟩, ⟨43, by omega⟩, ⟨15, by omega⟩]

theorem es_inj (e : ℕ) : Function.Injective (es e) := by
  intro i i' h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases i' <;> simp [es] at hv ⊢

theorem es_ne (e : ℕ) (i : Fin (16 + (46 + e))) (h1 : i.val ≠ 15) (h2 : i.val ≠ 42) (h3 : i.val ≠ 43) :
    ∀ l, es e l ≠ i := by
  intro l hl
  have hv := congrArg Fin.val hl
  fin_cases l <;> simp [es] at hv <;> omega

theorem ps_ne (e : ℕ) (i : Fin (16 + (46 + e))) (h : i.val < 16) : ∀ l, ps e l ≠ i := by
  intro l hl
  have hv := congrArg Fin.val hl
  simp only [ps] at hv
  omega

/-! ## The program's entry roles -/

section Entry
variable (w : List Bool) (offs : ℕ → ℕ) (P : ℕ)

/-- The program's entry roles. -/
def sIn : Fin (26 + 20) → TS := Fin.addCases (PacketsKeys.initRoles 26 w) (Prog.xin offs P)

theorem sIn_blank (W : ℕ) (j : Fin (26 + 20)) (h0 : j.val ≠ 0) (h1 : ¬ (36 ≤ j.val ∧ j.val < 44)) :
    TR W (sIn w offs P j) 0 [] := by
  unfold sIn
  induction j using Fin.addCases with
  | left i =>
    rw [Fin.addCases_left]
    unfold PacketsKeys.initRoles
    have hi0 : i.val ≠ 0 := by simpa using h0
    rw [if_neg hi0]
    by_cases hi1 : i.val = 1
    · rw [if_pos hi1]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hi1]
      exact ⟨rfl, fun j => read_nil j⟩
  | right i =>
    rw [Fin.addCases_right]
    have hv : ¬ (10 ≤ i.val ∧ i.val < 18) := by
      intro hh; apply h1; simp only [Fin.val_natAdd]; omega
    unfold Prog.xin
    by_cases a1 : i.val < 10
    · rw [if_pos a1]
      exact ⟨rfl, fun j => read_nil j⟩
    · rw [if_neg a1, if_neg (by omega), if_neg (by omega)]
      exact ⟨rfl, read_nil 0⟩

theorem sIn_off (j : Fin (26 + 20)) (h1 : 36 ≤ j.val) (h2 : j.val < 40) :
    sIn w offs P j = uw (offs (j.val - 36)) 0 := by
  have e : j = Fin.natAdd 26 ⟨j.val - 26, by omega⟩ := Fin.ext (by simp only [Fin.val_natAdd]; omega)
  conv_lhs => rw [e]
  unfold sIn
  rw [Fin.addCases_right]
  unfold Prog.xin
  simp only
  rw [if_neg (by omega), if_pos (by omega), show j.val - 26 - 10 = j.val - 36 by omega]

theorem sIn_len (j : Fin (26 + 20)) (h1 : 40 ≤ j.val) (h2 : j.val < 44) : sIn w offs P j = uw P 0 := by
  have e : j = Fin.natAdd 26 ⟨j.val - 26, by omega⟩ := Fin.ext (by simp only [Fin.val_natAdd]; omega)
  conv_lhs => rw [e]
  unfold sIn
  rw [Fin.addCases_right]
  unfold Prog.xin
  simp only
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

end Entry

/-! ## The cost -/

theorem symCost_le (m P : ℕ) : Prog.symCost (8 * m) m m P ≤ 20000 * (m + P + 1) ^ 2 := by
  unfold Prog.symCost Prog.blockWCost Win.tailCost PacketsKeys.Native.frontCost PacketsKeys.Native.headerCost
    PacketsKeys.Native.bodyCost PacketsKeys.Setup.cost
  nlinarith [Nat.zero_le m, Nat.zero_le P]

section Asm
variable (a : DecompositionAlgorithm) (wS : UnaryStage a (wOf a))

/-- The program part of the cost: the program, the exact copy (`|symBitsWord| ≤ 4·(pop+1)`). -/
def pc (R : Request) : ℕ :=
  Prog.symCost (8 * (fields a R 0).length) (fields a R 0).length (fields a R 0).length (pop a R + 1) + 1 +
    (4 * (pop a R + 1) + 1)

theorem pc_le (R : Request) : pc a R ≤ 80010 * (R.smallSize a) ^ 2 := by
  have h1 := symCost_le (fields a R 0).length (pop a R + 1)
  have h2 := PacketsKeys.Native.native_le_small a R
  have h3 : pop a R + 2 ≤ R.smallSize a := (PacketsCombine.small_facts (kitShapePG a) R).2.1
  unfold pc
  have h4 : ((fields a R 0).length + (pop a R + 1) + 1) ^ 2 ≤ (2 * R.smallSize a) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h5 : (2 * R.smallSize a) ^ 2 = 4 * (R.smallSize a) ^ 2 := by ring
  have h6 : R.smallSize a ≤ (R.smallSize a) ^ 2 := by nlinarith
  omega

/-- The machine: the vector, the program, the exact copy onto tape 15. -/
def symMachine :=
  Composition.machine (RecoveryFocus.machine (vs (symVec a wS).extra) (symVec a wS).machine)
    (Composition.machine (RecoveryFocus.machine (ps (symVec a wS).extra) Prog.symProg)
      (RecoveryFocus.machine (es (symVec a wS).extra) ExactCopy.machine))

/-- **The run at a SYM key.** -/
theorem sym_run (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r0 L target) (hk : k ∈ RCFive.RowKeys.symKeys r0 L target) :
    ∃ (H : Fin (16 + (46 + (symVec a wS).extra)) → ℕ) (A : Fin (16 + (46 + (symVec a wS).extra)) → List Bool),
      Step (symMachine a wS) ((symVec a wS).cost (.sym r0 four L target) + 1 + pc a (.sym r0 four L target))
        (fun _ => 0) (PacketsCombine.metaEntry a (.sym r0 four L target) (some k) (16 + (46 + (symVec a wS).extra)))
        H A ∧
      (∀ i : Fin (16 + (46 + (symVec a wS).extra)), i.val ≤ 8 →
        A i = PacketsCombine.metaEntry a (.sym r0 four L target) (some k) (16 + (46 + (symVec a wS).extra)) i ∧
          H i = 0) ∧
      (∀ t (ht : t < 6), A ⟨9 + t, by omega⟩ = symOuts a t (.sym r0 four L target) k ∧ H ⟨9 + t, by omega⟩ = 0) ∧
      A ⟨15, by omega⟩ = PacketsCombine.symBitsWord r0 L target k ∧
      H ⟨15, by omega⟩ = r0.circuits.length * ((symmetricFourfoldOccurrences r0).length + 1) := by
  obtain ⟨H1, A1, st1, keep1, out1⟩ := (symVec a wS).run (.sym r0 four L target) k hk
  -- the vector
  obtain ⟨H2, A2, st2, hs2, ho2⟩ := Dock.lift st1 (vs (symVec a wS).extra) (vs_inj _) (fun _ => 0) (fun _ => 0)
    (PacketsCombine.metaEntry a (.sym r0 four L target) (some k) (16 + (46 + (symVec a wS).extra))) (by
      intro j
      refine ⟨rfl, ?_⟩
      rw [ZeroPadding.pad_zero]
      by_cases h9 : j.val < 9
      · exact PacketsMeta.Keys.me_congr (Request.sym r0 four L target) (some k) _ _ (by rw [vs_val]; unfold vsV; rw [if_pos (by omega)])
      · rw [PacketsMeta.Keys.me_hi (Request.sym r0 four L target) (some k) _ (by rw [vs_val]; unfold vsV; split_ifs <;> omega),
          PacketsMeta.Keys.me_hi (Request.sym r0 four L target) (some k) _ (by omega)])
  have vw : ∀ t (ht : t < 15), A2 (vs (symVec a wS).extra ⟨9 + t, by omega⟩) = symOuts a t (.sym r0 four L target) k ∧
      H2 (vs (symVec a wS).extra ⟨9 + t, by omega⟩) = 0 := fun t ht =>
    ⟨(hs2 _).2.trans ((ZeroPadding.pad_zero _).trans (out1 t ht).1), (hs2 _).1.trans (out1 t ht).2⟩
  have bl : ∀ i : Fin (16 + (46 + (symVec a wS).extra)), (∀ j, vs (symVec a wS).extra j ≠ i) → 9 ≤ i.val →
      A2 i = [] ∧ H2 i = 0 := fun i hn h9 =>
    ⟨(ho2 i hn).2.trans (PacketsMeta.Keys.me_hi (Request.sym r0 four L target) (some k) _ h9), (ho2 i hn).1⟩
  -- the program's entry
  have hloc : ∀ j : Fin (26 + 20), TR (8 * (fields a (.sym r0 four L target) 0).length)
      (sIn (fields a (.sym r0 four L target) 0) (offsOf a (.sym r0 four L target) k) (pop a (.sym r0 four L target) + 1) j)
      (H2 (ps (symVec a wS).extra j)) (A2 (ps (symVec a wS).extra j)) := by
    intro j
    by_cases h0 : j.val = 0
    · have e : ps (symVec a wS).extra j = vs (symVec a wS).extra ⟨9 + 6, by omega⟩ :=
        Fin.ext (by simp only [ps, vs_val, vsV]; rw [h0]; rfl)
      rw [e, (vw 6 (by omega)).1, (vw 6 (by omega)).2]
      rcases j with ⟨jv, hjv⟩
      simp only at h0
      subst h0
      exact ⟨rfl, fun i => rfl⟩
    by_cases h1 : 36 ≤ j.val ∧ j.val < 40
    · have e : ps (symVec a wS).extra j = vs (symVec a wS).extra ⟨9 + (7 + (j.val - 36)), by omega⟩ :=
        Fin.ext (by simp only [ps, vs_val, vsV]; split_ifs <;> omega)
      rw [e, (vw _ (by omega)).1, (vw _ (by omega)).2, symOuts_off a (Request.sym r0 four L target) k _ (by omega), sIn_off _ _ _ j h1.1 h1.2]
      exact ⟨rfl, fun i => Win.read_rep _ i⟩
    by_cases h2 : 40 ≤ j.val ∧ j.val < 44
    · have e : ps (symVec a wS).extra j = vs (symVec a wS).extra ⟨9 + (11 + (j.val - 40)), by omega⟩ :=
        Fin.ext (by simp only [ps, vs_val, vsV]; split_ifs <;> omega)
      rw [e, (vw _ (by omega)).1, (vw _ (by omega)).2, symOuts_len a (Request.sym r0 four L target) k _ (by omega), sIn_len _ _ _ j h2.1 h2.2]
      exact ⟨rfl, fun i => Win.read_rep _ i⟩
    have hn : ∀ l, vs (symVec a wS).extra l ≠ ps (symVec a wS).extra j := by
      intro l hl
      have hv := congrArg Fin.val hl
      simp only [ps, vs_val, vsV] at hv
      split_ifs at hv <;> omega
    rw [(bl _ hn (by simp only [ps]; omega)).1, (bl _ hn (by simp only [ps]; omega)).2]
    exact sIn_blank _ _ _ _ j h0 (by omega)
  -- the program
  have hW1 : 1 ≤ (fields a (.sym r0 four L target) 0).length := PacketsKeys.Native.len_pos a _
  obtain ⟨b1, _, b3⟩ := PacketsKeys.Native.sym_bounds a r0 four L target
  have hlt := PacketsKeys.Native.small_lt _ hW1
  have hbw : ∀ c ∈ r0.circuits, c.bottomCount + 1 ≤ (fields a (.sym r0 four L target) 0).length := by
    intro c hc
    have e2 := PacketsKeys.Native.bc_le c
    have e3 := PacketsKeys.Native.mem_len_le r0.circuits (fun c => RepairOrdinary.frame (symWord c)) c hc
    have e4 : (r0.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))).length ≤
        (fields a (.sym r0 four L target) 0).length := by
      rw [PacketsKeys.Native.native_sym]; simp
    omega
  obtain ⟨σ', hl, ho, hm⟩ := Prog.symProg_run r0.q L target r0.circuits symWord (fun c => c.bottomCount)
    (fun c => List.ofFn c.top) (fun c => (List.ofFn c.bottom).flatMap (fun g => RepairOrdinary.frame (bottomWord g)))
    (fields a (.sym r0 four L target) 0) (PacketsKeys.Native.native_sym a r0 four L target)
    (fun c => by simp only [symWord, List.append_assoc])
    (by
      intro c hc
      have e1 := PacketsKeys.Native.nbl_le_self c.bottomCount
      have := hbw c hc
      omega)
    (lt_of_le_of_lt b1 hlt) b3 (offsOf a (.sym r0 four L target) k) (pop a (.sym r0 four L target) + 1)
    (fields a (.sym r0 four L target) 0).length (by
      intro d hd
      have h1 : offsOf a (.sym r0 four L target) k d = k.offset ⟨d, hd⟩ := offsOf_sym a r0 four L target k ⟨d, hd⟩
      have h2 := offset_le r0 L target k hk ⟨d, hd⟩
      have h3 := hbw (r0.circuits.get ⟨d, hd⟩) (List.get_mem _ _)
      omega)
  obtain ⟨Hl, Al, stp, trs⟩ := hl (fun j => H2 (ps (symVec a wS).extra j)) (fun j => A2 (ps (symVec a wS).extra j)) hloc
  obtain ⟨H3, A3, st3, hs3, ho3⟩ := Dock.lift stp (ps (symVec a wS).extra) (ps_inj _) (fun _ => 0) H2 A2
    (fun j => ⟨rfl, (ZeroPadding.pad_zero _).symm⟩)
  -- the exact copy
  have tro := trs (Prog.ex 0 (by omega))
  rw [ho] at tro
  have tm := trs (Prog.ex 1 (by omega))
  rw [hm] at tm
  obtain ⟨to1, to2⟩ := tro
  obtain ⟨tm1, tm2⟩ := tm
  have n15v : ∀ l, vs (symVec a wS).extra l ≠ ⟨15, by omega⟩ := by
    intro l hl
    have hv := congrArg Fin.val hl
    simp only [vs_val, vsV] at hv
    split_ifs at hv <;> omega
  have n15p : ∀ l, ps (symVec a wS).extra l ≠ ⟨15, by omega⟩ := ps_ne _ _ (by simp)
  obtain ⟨H4, A4, st4, hs4, ho4⟩ := Dock.lift
    (ExactCopy.run (Al (Prog.ex 0 (by omega))) (Al (Prog.ex 1 (by omega))) []
      (Prog.outAt r0.circuits (fun c => List.ofFn c.top) (offsOf a (.sym r0 four L target) k)
        (pop a (.sym r0 four L target) + 1) 4) to2 tm2)
    (es (symVec a wS).extra) (es_inj _) (fun _ => 0) H3 A3 (by
      intro i
      fin_cases i
      · have e : es (symVec a wS).extra 0 = ps (symVec a wS).extra (Prog.ex 0 (by omega)) := Fin.ext rfl
        show H3 (es (symVec a wS).extra 0) = 1 ∧ A3 (es (symVec a wS).extra 0) = ZeroPadding.pad 0 (Al (Prog.ex 0 (by omega)))
        rw [e, (hs3 _).1, (hs3 _).2, to1]
        exact ⟨rfl, rfl⟩
      · have e : es (symVec a wS).extra 1 = ps (symVec a wS).extra (Prog.ex 1 (by omega)) := Fin.ext rfl
        show H3 (es (symVec a wS).extra 1) = 1 ∧ A3 (es (symVec a wS).extra 1) = ZeroPadding.pad 0 (Al (Prog.ex 1 (by omega)))
        rw [e, (hs3 _).1, (hs3 _).2, tm1]
        exact ⟨rfl, rfl⟩
      · have e : es (symVec a wS).extra 2 = ⟨15, by omega⟩ := Fin.ext rfl
        show H3 (es (symVec a wS).extra 2) = 0 ∧ A3 (es (symVec a wS).extra 2) = ZeroPadding.pad 0 []
        rw [e, (ho3 _ n15p).1, (ho3 _ n15p).2, (bl _ n15v (by simp)).1, (bl _ n15v (by simp)).2]
        exact ⟨rfl, rfl⟩)
  have hml := Prog.outAt_length_le r0.circuits (fun c => List.ofFn c.top) (offsOf a (.sym r0 four L target) k)
    (pop a (.sym r0 four L target) + 1) 4
  have hsb : Prog.outAt r0.circuits (fun c => List.ofFn c.top) (offsOf a (.sym r0 four L target) k)
      (pop a (.sym r0 four L target) + 1) 4 = PacketsCombine.symBitsWord r0 L target k := symBits_eq a r0 four L target k
  refine ⟨H4, A4, (st2.seq (st3.seq st4)).enlarge ?_, ?_, ?_, ?_, ?_⟩
  · unfold pc
    omega
  · intro i hi
    have n1 := es_ne (symVec a wS).extra i (by omega) (by omega) (by omega)
    have n2 := ps_ne (symVec a wS).extra i (by omega)
    have e : i = vs (symVec a wS).extra ⟨i.val, by omega⟩ :=
      Fin.ext (by rw [vs_val]; show i.val = vsV i.val; unfold vsV; rw [if_pos (by omega)])
    have hlt : (⟨i.val, by omega⟩ : Fin (9 + 15 + (symVec a wS).extra)).val < 9 := by show i.val < 9; omega
    refine ⟨?_, ?_⟩
    · rw [(ho4 _ n1).2, (ho3 _ n2).2]
      have h := (hs2 ⟨i.val, by omega⟩).2
      rw [← e] at h
      rw [h, ZeroPadding.pad_zero, (keep1 _ hlt).1]
      exact PacketsMeta.Keys.me_congr (Request.sym r0 four L target) (some k) _ _ rfl
    · rw [(ho4 _ n1).1, (ho3 _ n2).1]
      have h := (hs2 ⟨i.val, by omega⟩).1
      rw [← e] at h
      rw [h, (keep1 _ hlt).2]
  · intro t ht
    have n1 := es_ne (symVec a wS).extra ⟨9 + t, by omega⟩ (by show 9 + t ≠ 15; omega) (by show 9 + t ≠ 42; omega)
      (by show 9 + t ≠ 43; omega)
    have n2 := ps_ne (symVec a wS).extra ⟨9 + t, by omega⟩ (by show 9 + t < 16; omega)
    have e : (⟨9 + t, by omega⟩ : Fin (16 + (46 + (symVec a wS).extra))) = vs (symVec a wS).extra ⟨9 + t, by omega⟩ :=
      Fin.ext (by rw [vs_val]; show 9 + t = vsV (9 + t); unfold vsV; rw [if_pos (by omega)])
    rw [(ho4 _ n1).1, (ho4 _ n1).2, (ho3 _ n2).1, (ho3 _ n2).2, e]
    exact vw t (by omega)
  · have e : (⟨15, by omega⟩ : Fin (16 + (46 + (symVec a wS).extra))) = es (symVec a wS).extra 2 := Fin.ext rfl
    rw [e, (hs4 2).2, ZeroPadding.pad_zero]
    show [] ++ _ = _
    rw [List.nil_append, hsb]
  · have e : (⟨15, by omega⟩ : Fin (16 + (46 + (symVec a wS).extra))) = es (symVec a wS).extra 2 := Fin.ext rfl
    rw [e, (hs4 2).1]
    show ([] : List Bool).length + _ = _
    rw [List.length_nil, Nat.zero_add, hsb, symBits_length]

def symMetaPG : PacketsCombine.SymMeta a (kitShapePG a) where
  extra := 46 + (symVec a wS).extra
  states := _
  machine := symMachine a wS
  cost := fun R => (symVec a wS).cost R + 1 + pc a R
  coefficient := (symVec a wS).costC + 1 + 80010
  degree := (symVec a wS).costD + 2
  cost_le := fun R => PacketsCombine.Asm.sum_le _ _ _ _ _ _ _ (one_le_small a R) ((symVec a wS).cost_le R) (pc_le a R)
  run := by
    intro r four L target k hk
    obtain ⟨H, A, st, keep, tpl, h15, hh15⟩ := sym_run a wS r four L target k hk
    exact ⟨H, A, st, keep, (tpl 0 (by omega)).1, (tpl 0 (by omega)).2, (tpl 1 (by omega)).1, (tpl 1 (by omega)).2,
      (tpl 2 (by omega)).1, (tpl 2 (by omega)).2, (tpl 3 (by omega)).1, (tpl 3 (by omega)).2,
      (tpl 4 (by omega)).1, (tpl 4 (by omega)).2, (tpl 5 (by omega)).1, (tpl 5 (by omega)).2, h15, hh15⟩

end Asm

end
end NearCubicWires.PacketsSymBits.Meta

