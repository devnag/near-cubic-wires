import Proof.Packets.PacketsKeysThrBounds
import Proof.Packets.PacketsKeysThrSpec
import Proof.Packets.PacketsMetaKeyWords

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
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.ThresholdAlignedEnvelope NearCubicWires.PacketsKeys.RM NearCubicWires.PacketsKeys.ThrProg
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

variable (a : DecompositionAlgorithm)

/-! ## The key vector -/

/-- `frame topWord`. -/
def tkTop : PacketsCombine.Asm.ThrWord a (fun r four L target _ => RepairOrdinary.frame (fields a (.thr r four L target) 4)) :=
  PacketsCombine.Asm.ThrWord.ofKeyWord (KeyWord.ofWord (fieldFrame a 4)) _ (fun _ _ _ _ _ => rfl)

/-- `1^p`. -/
def tkPrime : PacketsCombine.Asm.ThrWord a (fun _ _ _ _ k => List.replicate k.prime.val true) :=
  PacketsCombine.Asm.ThrWord.ofKeyWord (PacketsMeta.Keys.primeW a) _
    (fun r four L target k => PacketsMeta.Keys.primeW_thr a r four L target k)

/-- `1^(sel c)`: key digit `c`. -/
def tkSelW (c : Fin 4) : PacketsCombine.Asm.ThrWord a
    (fun r four L target k => List.replicate (keyDigits a (.thr r four L target) (some k) ⟨c.val, by omega⟩) true) :=
  PacketsCombine.Asm.ThrWord.ofKeyWord (PacketsMeta.Keys.fieldKey a ⟨c.val, by omega⟩) _ (fun _ _ _ _ _ => rfl)

/-- The eight words (in the shape `ThrVec.snoc` builds). -/
def tkOuts : ℕ → PacketsCombine.Asm.TVal a := fun t =>
  if t = 7 then (fun r four L target k => List.replicate (keyDigits a (.thr r four L target) (some k) ⟨(3 : Fin 4).val, by omega⟩) true)
  else if t = 6 then (fun r four L target k => List.replicate (keyDigits a (.thr r four L target) (some k) ⟨(2 : Fin 4).val, by omega⟩) true)
  else if t = 5 then (fun r four L target k => List.replicate (keyDigits a (.thr r four L target) (some k) ⟨(1 : Fin 4).val, by omega⟩) true)
  else if t = 4 then (fun r four L target k => List.replicate (keyDigits a (.thr r four L target) (some k) ⟨(0 : Fin 4).val, by omega⟩) true)
  else if t = 3 then (fun _ _ _ _ k => List.replicate k.prime.val true)
  else if t = 2 then (fun _ _ _ _ k => List.replicate k.prime.val true)
  else if t = 1 then (fun _ _ _ _ k => List.replicate k.prime.val true)
  else if t = 0 then (fun r four L target _ => RepairOrdinary.frame (fields a (.thr r four L target) 4))
  else (fun _ _ _ _ _ => [])

/-- **The key vector** (one fixed machine). -/
def tkVec : PacketsCombine.Asm.ThrVec a 8 (tkOuts a) :=
  ((((((((PacketsCombine.Asm.ThrVec.nil a (fun _ _ _ _ _ _ => [])).snoc (tkTop a)).snoc (tkPrime a)).snoc
    (tkPrime a)).snoc (tkPrime a)).snoc (tkSelW a 0)).snoc (tkSelW a 1)).snoc (tkSelW a 2)).snoc (tkSelW a 3)

/-! ## Per-request quantities -/

/-- The key's prime (THR), `0` otherwise. -/
def tkP : ∀ r : Request, rcKey a r → ℕ
  | .thr r _ L target, k => (k : RCFive.RowKeys.ThrKey a r L target).prime.val
  | .sym _ _ _ _, _ => 0
  | .terminal, _ => 0

/-- The key's four selection digits. -/
def tkSel (r : Request) (k : rcKey a r) (c : Fin 4) : ℕ := keyDigits a r (some k) ⟨c.val, by omega⟩

/-- The program's width. -/
def tkWd (r : Request) (k : rcKey a r) (_ : ℕ) : ℕ := 8 * (fields a r 4).length + tkP a r k + tkP a r k

/-- The program's step count. -/
def tkPn (r : Request) (k : rcKey a r) (j : ℕ) : ℕ :=
  thrCost (tkWd a r k j) (fields a r 4).length (tkP a r k) j (tkSel a r k) ((maskBitsList a r k).getD j []).length

/-- The width bound of a request (the cutoff in place of the prime). -/
def tkWr (r : Request) : ℕ := 8 * (fields a r 4).length + cutoffOf a r + cutoffOf a r

/-- The per-request step bound. -/
def tkPc (r : Request) : ℕ := 100000 * (tkWr a r + 1) ^ 3 + 3 * tkWr a r + 10

/-! ## The entry state -/

/-- The program's entry state, read off the eight words. -/
def tkZ (w : ℕ → List Bool) (j : ℕ) : TZ where
  rl := bl
  fl := false
  P := 0
  A := 0
  K := 0
  I := 0
  X := 0
  B := 0
  Bm := 0
  F := 0
  R := 0
  M := 0
  T := 0
  MSK := 0
  MT := 0
  MM := 0
  E := 0
  Ep := 0
  E2m := 0
  Em := 0
  Jc := 0
  SG := 0
  S := fun _ => 0
  ts := bl
  tm := bl
  os := bl
  om := bl
  js := .cells (sf (List.replicate (j + 1) true)) 1
  jd := bl
  tf := .cells (fun i => readTapeBit (w 0) i) 0
  up1 := .cells (fun i => readTapeBit (w 1) i) 0
  d1 := bl
  up1' := .cells (fun i => readTapeBit (w 2) i) 0
  d1' := bl
  up2 := .cells (fun i => readTapeBit (w 3) i) 0
  d2 := bl
  us := fun c => .cells (fun i => readTapeBit (w (4 + c.val)) i) 0
  ds := fun _ => bl
  cc := fun _ => bl

/-- The program's entry roles. -/
def tkIn (r : Request) (k : rcKey a r) (j : ℕ) : Fin (4 + 24 + 29) → TS :=
  roles (toSt (tkZ (fun t => thrOuts (tkOuts a) t r k) j))

/-- The words' slots. -/
def tkSlot : Fin 8 → Fin (4 + 24 + 29) :=
  ![os oTF, os oUP1, os oUP1', os oUP2, os (oUS 0), os (oUS 1), os (oUS 2), os (oUS 3)]

theorem rtb_rep (n j : ℕ) : readTapeBit (List.replicate n true) j = decide (j < n) := by
  unfold readTapeBit
  by_cases h : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]; simp [h]

theorem tkZ_thr (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) (k : rcKey a (.thr r0 four L target)) (j : ℕ) :
    tkZ (fun t => thrOuts (tkOuts a) t (.thr r0 four L target) k) j =
      zIn (fields a (.thr r0 four L target) 4) (tkP a (.thr r0 four L target) k) (tkSel a (.thr r0 four L target) k) j := by
  unfold tkZ zIn
  congr 1
  · congr 1; funext i; exact rtb_rep _ i
  · congr 1; funext i; exact rtb_rep _ i
  · congr 1; funext i; exact rtb_rep _ i
  · funext c
    fin_cases c <;> (congr 1; funext i; exact rtb_rep _ i)

theorem tk_hwr (r : Request) (k : rcKey a r) (j : ℕ) (t : Fin 8) :
    tkIn a r k j (tkSlot t) = .cells (fun i => readTapeBit (thrOuts (tkOuts a) t.val r k) i) 0 := by
  fin_cases t <;> rfl

theorem tk_hjr (r : Request) (k : rcKey a r) (j : ℕ) :
    tkIn a r k j (os oJS) = .cells (sf (List.replicate (j + 1) true)) 1 := rfl

theorem tk_hbr (r : Request) (k : rcKey a r) (j W : ℕ) (i : Fin (4 + 24 + 29)) (h1 : ∀ t, tkSlot t ≠ i)
    (h2 : i ≠ os oJS) : TR W (tkIn a r k j i) 0 [] := by
  have hreg : TR W (.reg 0) 0 [] := ⟨rfl, fun j _ _ => by rw [read_nil, Nat.zero_testBit]⟩
  have hbl : TR W (.cells blank 0) 0 [] := ⟨rfl, fun j => read_nil j⟩
  have hfl : TR W (.flag false) 0 [] := ⟨rfl, read_nil 0⟩
  fin_cases i <;> first
    | exact absurd rfl (h1 0) | exact absurd rfl (h1 1) | exact absurd rfl (h1 2) | exact absurd rfl (h1 3)
    | exact absurd rfl (h1 4) | exact absurd rfl (h1 5) | exact absurd rfl (h1 6) | exact absurd rfl (h1 7)
    | exact absurd rfl h2 | exact hreg | exact hbl | exact hfl

/-! ## THR requests: the circuits' words and the digits -/

/-- A circuit's arity. -/
def arT {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) : ℕ := c.top.support.card

/-- A circuit's children. -/
def chT {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) : List (ExactThresholdGate (arT c)) :=
  ThresholdRows.children a c

section Thr
variable (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4) (L target : ℕ)
  (k : rcKey a (.thr r0 four L target))

theorem tw_thr : twOf arT (chT a) r0.circuits = fields a (.thr r0 four L target) 4 := by
  rw [Native.top_thr a r0 four L target]
  unfold twOf
  congr 1
  funext c
  rw [Native.tpay_split]
  rfl

theorem tkSel_lt (c : Fin 4) (hc : c.val < r0.circuits.length) :
    tkSel a (.thr r0 four L target) k c = (k.selection ⟨c.val, hc⟩).val := by
  unfold tkSel
  rw [keyDigits_thr]
  exact dif_pos hc

theorem tkSel_ge (c : Fin 4) (hc : r0.circuits.length ≤ c.val) : tkSel a (.thr r0 four L target) k c = 0 := by
  have h4 := c.isLt
  unfold tkSel
  rw [keyDigits_thr]
  simp only [Fin.val_mk]
  split_ifs <;> omega

theorem tkSel_le (c : Fin 4) : tkSel a (.thr r0 four L target) k c ≤ (twOf arT (chT a) r0.circuits).length := by
  by_cases hc : c.val < r0.circuits.length
  · rw [tkSel_lt a r0 four L target k c hc]
    have h1 : (k.selection ⟨c.val, hc⟩).val < (chT a r0.circuits[c.val]).length := (k.selection _).isLt
    have h2 := ch_le_pay arT (chT a) r0.circuits[c.val]
    have h3 := pay_le_tw arT (chT a) r0.circuits r0.circuits[c.val] (by simp)
    omega
  · rw [tkSel_ge a r0 four L target k c (by omega)]
    omega

theorem msOf_thr : 1 + (msOf arT (chT a) r0.circuits (tkSel a (.thr r0 four L target) k)).sum =
    Thr.baseN a r0 k.selection := by
  have e : msOf arT (chT a) r0.circuits (tkSel a (.thr r0 four L target) k) = List.ofFn (fun i : Fin r0.circuits.length =>
      childMagnitude ((ThresholdRows.children a (r0.circuits.get i)).get (k.selection i))) := by
    apply List.ext_getElem (by simp [msOf])
    intro n h1 h2
    have hn : n < r0.circuits.length := by simpa using h2
    rw [msOf_get' arT (chT a) r0.circuits _ n hn (by omega) (k.selection ⟨n, hn⟩).val
      (tkSel_lt a r0 four L target k ⟨n, by omega⟩ hn) (k.selection ⟨n, hn⟩).isLt, List.getElem_ofFn]
    rfl
  rw [e, List.sum_ofFn]
  unfold Thr.baseN
  omega

theorem outK_thr (j : ℕ) :
    outK arT (chT a) r0.circuits (tkSel a (.thr r0 four L target) k)
      (1 + (msOf arT (chT a) r0.circuits (tkSel a (.thr r0 four L target) k)).sum) k.prime.val j 4 =
      Thr.thrBits a r0 k.selection k.prime.val j := by
  rw [msOf_thr a r0 four L target k, outK_eq arT (chT a) r0.circuits four]
  unfold Thr.thrBits
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  have hn : n < r0.circuits.length := by simpa using h1
  simp only [List.getElem_ofFn]
  rw [bitsAt_of arT (chT a) r0.circuits _ _ _ _ n hn (by omega) (k.selection ⟨n, hn⟩).val
    (tkSel_lt a r0 four L target k ⟨n, by omega⟩ hn) (k.selection ⟨n, hn⟩).isLt, List.map_ofFn]
  rfl

theorem thr_count : maskCount a (.thr r0 four L target) k = modulusDigitCount k.prime.val := by
  rw [← maskBitsList_length]
  simp [maskBitsList, thrMasks]

/-- **The program's output is the mask.** -/
theorem outK_mask (j : ℕ) (hj : j < maskCount a (.thr r0 four L target) k) :
    outK arT (chT a) r0.circuits (tkSel a (.thr r0 four L target) k)
      (1 + (msOf arT (chT a) r0.circuits (tkSel a (.thr r0 four L target) k)).sum) k.prime.val j 4 =
      (maskBitsList a (.thr r0 four L target) k).getD j [] := by
  rw [outK_thr a r0 four L target k j,
    Thr.thr_bits a r0 four L target k j (by rw [← thr_count a r0 four L target k]; exact hj)]

theorem prime_facts (j : ℕ) (hj : j < maskCount a (.thr r0 four L target) k) :
    2 ≤ k.prime.val ∧ j + 1 ≤ k.prime.val ∧ k.prime.val ≤ cutoffOf a (.thr r0 four L target) := by
  have hm := mem_primesUpTo.mp k.prime.property
  have hj' : j < modulusDigitCount k.prime.val := by rw [← thr_count a r0 four L target k]; exact hj
  have hp0 : k.prime.val ≠ 0 := hm.1.ne_zero
  have h1 : 2 ^ Nat.log 2 k.prime.val ≤ k.prime.val := Nat.pow_log_le_self 2 hp0
  have h2 : Nat.log 2 k.prime.val < 2 ^ Nat.log 2 k.prime.val := Nat.lt_two_pow_self
  unfold modulusDigitCount at hj'
  exact ⟨hm.1.two_le, by omega, hm.2⟩

end Thr

/-! ## The two premises of the assembly -/

theorem tk_hrun (r : Request) (hp : IsThr r) (k : rcKey a r) (_ : k ∈ rcKeys a r) (j : ℕ) (hj : j < maskCount a r k) :
    ∃ σ' : Fin (4 + 24 + 29) → TS, LRuns (tkWd a r k j) thrProg (tkPn a r k j) (tkIn a r k j) σ' ∧
      σ' (os oOS) = .cells (sf ((maskBitsList a r k).getD j [])) 1 ∧
      σ' (os oOM) = .cells (sf (List.replicate ((maskBitsList a r k).getD j []).length true)) 1 := by
  cases r with
  | terminal => exact hp.elim
  | sym _ _ _ _ => exact hp.elim
  | thr r0 four L target =>
    obtain ⟨hp2, hj1, _⟩ := prime_facts a r0 four L target k j hj
    obtain ⟨σ', hl, ho, hm⟩ := thrRun arT (chT a) r0.circuits four k.prime.val hp2 (tkSel a (.thr r0 four L target) k) j
      hj1 (fun i hi => by rw [tkSel_lt a r0 four L target k i hi]; exact (k.selection _).isLt)
      (tkSel_le a r0 four L target k)
    rw [outK_mask a r0 four L target k j hj] at hl ho hm
    rw [tw_thr a r0 four L target] at hl
    refine ⟨σ', ?_, ho, hm⟩
    show LRuns (8 * (fields a (.thr r0 four L target) 4).length + k.prime.val + k.prime.val) thrProg
      (thrCost (8 * (fields a (.thr r0 four L target) 4).length + k.prime.val + k.prime.val)
        (fields a (.thr r0 four L target) 4).length k.prime.val j (tkSel a (.thr r0 four L target) k)
        ((maskBitsList a (.thr r0 four L target) k).getD j []).length)
      (roles (toSt (tkZ (fun t => thrOuts (tkOuts a) t (.thr r0 four L target) k) j))) σ'
    rw [tkZ_thr a r0 four L target k j]
    exact hl

theorem tk_hpc (r : Request) (hp : IsThr r) (k : rcKey a r) (_ : k ∈ rcKeys a r) (j : ℕ)
    (hj : j < maskCount a r k) :
    2 * j + 4 + 1 + (tkPn a r k j + 1 + (((maskBitsList a r k).getD j []).length + 1)) ≤ tkPc a r := by
  cases r with
  | terminal => exact hp.elim
  | sym _ _ _ _ => exact hp.elim
  | thr r0 four L target =>
    obtain ⟨hp2, hj1, hcut⟩ := prime_facts a r0 four L target k j hj
    have hv := outK_len_le arT (chT a) r0.circuits four (tkSel a (.thr r0 four L target) k)
      (1 + (msOf arT (chT a) r0.circuits (tkSel a (.thr r0 four L target) k)).sum) k.prime.val j
    rw [outK_mask a r0 four L target k j hj, tw_thr a r0 four L target] at hv
    have hsl : ∀ c, tkSel a (.thr r0 four L target) k c ≤ (fields a (.thr r0 four L target) 4).length := by
      intro c
      have := tkSel_le a r0 four L target k c
      rwa [tw_thr a r0 four L target] at this
    have hc := thrCost_le (8 * (fields a (.thr r0 four L target) 4).length + k.prime.val + k.prime.val)
      (fields a (.thr r0 four L target) 4).length k.prime.val j
      ((maskBitsList a (.thr r0 four L target) k).getD j []).length (tkSel a (.thr r0 four L target) k)
      (by omega) (by omega) (by omega) (fun c => by have := hsl c; omega) (by omega)
    have hW : 8 * (fields a (.thr r0 four L target) 4).length + k.prime.val + k.prime.val + 1 ≤
        tkWr a (.thr r0 four L target) + 1 := by
      unfold tkWr; omega
    have hpow := Nat.pow_le_pow_left hW 3
    show 2 * j + 4 + 1 + (thrCost (8 * (fields a (.thr r0 four L target) 4).length + k.prime.val + k.prime.val)
      (fields a (.thr r0 four L target) 4).length k.prime.val j (tkSel a (.thr r0 four L target) k)
      ((maskBitsList a (.thr r0 four L target) k).getD j []).length + 1 +
      (((maskBitsList a (.thr r0 four L target) k).getD j []).length + 1)) ≤ tkPc a (.thr r0 four L target)
    unfold tkPc
    unfold tkWr at hW hpow ⊢
    omega

/-! ## Cost -/

theorem cutoff_small (r : Request) : cutoffOf a r ≤ 40000 * (r.smallSize a) ^ 3 := by
  cases r with
  | terminal => exact Nat.zero_le _
  | sym _ _ _ _ => exact Nat.zero_le _
  | thr r0 four L target =>
    show CloseoutFinalC10ThresholdRows.primeCutoff a r0 target ≤ _
    rw [← NearCubicWires.PacketsMeta.Spec.cut_eq a r0 four target]
    exact NearCubicWires.PacketsMeta.Stage.cut_le_small a r0 four L target

theorem tkWr_le (r : Request) : tkWr a r + 1 ≤ 80009 * (r.smallSize a) ^ 3 := by
  have h1 := field_le_input a r 4
  have h2 := input_le_small a r
  rw [RepairOrdinary.frame_length] at h1
  have h3 := cutoff_small a r
  have hS := one_le_small a r
  have hS3 : r.smallSize a ≤ (r.smallSize a) ^ 3 := by
    calc r.smallSize a = (r.smallSize a) ^ 1 := (pow_one _).symm
      _ ≤ (r.smallSize a) ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  unfold tkWr
  omega

theorem tkPc_le (r : Request) : tkPc a r ≤ 51217281944073700090 * (r.smallSize a) ^ 9 := by
  have h := tkWr_le a r
  have h3 : (tkWr a r + 1) ^ 3 ≤ (80009 * (r.smallSize a) ^ 3) ^ 3 := Nat.pow_le_pow_left h 3
  have e : (80009 * (r.smallSize a) ^ 3) ^ 3 = 512172819440729 * (r.smallSize a) ^ 9 := by ring
  have hS := one_le_small a r
  have hS9 : (r.smallSize a) ^ 3 ≤ (r.smallSize a) ^ 9 := Nat.pow_le_pow_right hS (by norm_num)
  unfold tkPc
  omega

/-! ## The stage -/

def thrMask : KeyStageOn a IsThr (fun r k j => (maskBitsList a r k).getD j []) :=
  KeyStageOn.ofProg (KVecOn.ofThrVec (tkVec a)) thrProg tkSlot (os oJS) (os oOS) (os oOM)
    (by decide) (by decide) (by decide)
    (tkWd a) (tkPn a) (tkIn a) (tk_hrun a) (tk_hwr a) (tk_hjr a)
    (fun r k j i h1 h2 => tk_hbr a r k j _ i h1 h2)
    (tkPc a) (tk_hpc a) 51217281944073700090 9 (tkPc_le a)

end
end NearCubicWires.PacketsKeys.Stage

