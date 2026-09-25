import Proof.Rows.RowsInitThrInitReady
import Proof.Rows.RowsInitC5
import Proof.Packets.PacketsCircBound
import Proof.Packets.PacketsKeyWords

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.FrameSymWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.BlockPlatform
open NearCubicWires.SupplierPipeline NearCubicWires.PacketFamilyParent
open RowsConstruction RowsConstruction.BaseLayout RowsInit.VecDock
open RowsInit.ThrInitRun (inst_at inst_off)
open RowsInit.ThrLoop (wp wp_val vmap vmap_val vmap_inj rw_eq)
noncomputable section

/-! ## 1. The word stages -/

section Stages
variable (a : DecompositionAlgorithm)

/-- `1^(T+3)` (`T = |input|`, the SYM counter width `sw`). -/
def t3S : UnaryStage a (fun r => (r.input a).length + 3) :=
  (inputLenStage a).thenMapP (plusMap 3) (2 * 3 + 4) 1 (plus_cost 3)

/-- Offset bound `c`: `frame (resize (T+3) (bits (circBound a c r)))` (`= fb (T+3) (sbnd r c)` on SYM, `sym_ready`). -/
def bndS (c : Fin 4) : WordStage a (fun r => frame (ClockNormalize.resize ((r.input a).length + 3)
    (CloseoutRowsCountBinary.bits (PacketsGlue.CursorChain.circBound a c.val r)))) :=
  (t3S a).pairWP (PacketsConstruction.CircBound.circBoundStage a c) RowsInit.BinWords.binMap2 100 2
    RowsInit.BinWords.bin_cost

theorem bit_cost (x : ℕ) : bitWordMap.cost x ≤ 1 * (x + 3) ^ 0 := by
  simp [bitWordMap]

/-- Target flag `c`: `[decide (0 < n - c)]` (`n = #circuits`; `= [decide (c < n)]`). -/
def flagS (c : ℕ) : WordStage a (fun r => [decide (0 < PacketsKeys.Native.nCirc r - c)]) :=
  ((PacketsKeys.Native.circuitsStage a).pairP (PacketsConstruction.CircBound.constS a c)
    PacketsConstruction.CircBound.monusMap2 6 1 PacketsConstruction.CircBound.monus_cost).thenWordP bitWordMap 1 0 bit_cost

/-- `fb (T+3) 0`. -/
def zS : WordStage a (fun r => frame (SignedSortKey.binary ((r.input a).length + 3) 0)) :=
  (t3S a).thenWordP zeroWordMap 8 1 zero_cost

/-- The SYM mode flag `[false]`. -/
def falseS : WordStage a (fun _ => [false]) :=
  RowsInit.LoopWords.wofEq ((PacketsConstruction.CircBound.zeroS a).thenWordP bitWordMap 1 0 bit_cost) (fun _ => rfl)

end Stages

/-! ## 2. The 14 words -/

/-- **The SYM request-constant words** (table): 0–3 `fb (T+3) (circBound c)` (resized), 4–7 `[decide (0 < n - c)]`, 8 `fb (T+3) 0`,
9 `[false]`, 10–13 `fb (T+3) 0` (the C5 offsets). -/
def symWord (a : DecompositionAlgorithm) (j : Fin 14) (r : Request) : List Bool :=
  let T := (r.input a).length
  match j.val with
  | 0 => frame (ClockNormalize.resize (T + 3) (CloseoutRowsCountBinary.bits (PacketsGlue.CursorChain.circBound a 0 r)))
  | 1 => frame (ClockNormalize.resize (T + 3) (CloseoutRowsCountBinary.bits (PacketsGlue.CursorChain.circBound a 1 r)))
  | 2 => frame (ClockNormalize.resize (T + 3) (CloseoutRowsCountBinary.bits (PacketsGlue.CursorChain.circBound a 2 r)))
  | 3 => frame (ClockNormalize.resize (T + 3) (CloseoutRowsCountBinary.bits (PacketsGlue.CursorChain.circBound a 3 r)))
  | 4 => [decide (0 < PacketsKeys.Native.nCirc r - 0)]
  | 5 => [decide (0 < PacketsKeys.Native.nCirc r - 1)]
  | 6 => [decide (0 < PacketsKeys.Native.nCirc r - 2)]
  | 7 => [decide (0 < PacketsKeys.Native.nCirc r - 3)]
  | 9 => [false]
  | _ => frame (SignedSortKey.binary (T + 3) 0)

/-- **The 14 words by ONE fixed machine** (the `snoc` chain). -/
def symVec (a : DecompositionAlgorithm) :=
  ((((((((((((((VecStage.nil a (fun _ _ => [])).snoc (bndS a 0)).snoc (bndS a 1)).snoc (bndS a 2)).snoc
    (bndS a 3)).snoc (flagS a 0)).snoc (flagS a 1)).snoc (flagS a 2)).snoc (flagS a 3)).snoc (zS a)).snoc
    (falseS a)).snoc (zS a)).snoc (zS a)).snoc (zS a)).snoc (zS a)

/-! ## 3. The docked machine -/

/-- The value map: request (pub 0), words 0–9 to `init 136..145` (work 138–147), 10–13 to C5 3–6, scratch from `init oB`. -/
def dst (NI oB v : ℕ) : ℕ :=
  if v = 0 then 0 else if v ≤ 10 then 137 + v else if v ≤ 14 then 2 + NI + 594 + 3 + (v - 11) else 2 + oB + (v - 15)

section Maps
variable (a : DecompositionAlgorithm) (NI oB : ℕ)

/-- The scratch the stage needs past `oB` (the vector's private tapes and the mask tape). -/
def needW : ℕ := (symVec a).extra + 1

def sl := vmap NI (1 + 14 + (symVec a).extra + 1) (dst NI oB)

variable (hB : 146 ≤ oB) (hN : oB + needW a ≤ NI)
include hN

theorem bd : ∀ v, v < 1 + 14 + (symVec a).extra + 1 → dst NI oB v < 2 + rowsWork NI := by
  intro v hv; unfold needW at hN; rw [rw_eq]; unfold dst; split_ifs <;> omega

include hB in
theorem sl_inj : Function.Injective (sl a NI oB) := vmap_inj (bd a NI oB hN) (by
  intro v w _ _ h; unfold needW at hN; unfold dst at h; split_ifs at h <;> omega)

end Maps

/-- **The SYM word writer** (one fixed machine per `a`, `NI`, `oB`). -/
def machine (a : DecompositionAlgorithm) (NI oB : ℕ) :=
  RecoveryFocus.machine (sl a NI oB) (MaskedReset.machine (symVec a).machine (fun _ => true))

def cost (a : DecompositionAlgorithm) (r : Request) : ℕ := 2 * (symVec a).cost r + 2

theorem c5_val (NI : ℕ) (i : Fin 16) : (c5Port NI i).val = 2 + NI + 594 + i.val := RowsInit.C5.c5_val NI i

/-- **The run.** Entry: pub 0 = framed request; the fixed ports 138–147 (`init 136..145`), C5 3–6 and the scratch
`[oB, oB + needW)` blank; heads `0`. Exit: `init (136+j)` = word `j` (j < 10), C5 3–6 = `fb (T+3) 0`, nothing else moved. -/
theorem words_run (a : DecompositionAlgorithm) (NI oB : ℕ) (hB : 146 ≤ oB) (hN : oB + needW a ≤ NI) (r : Request)
    (A : Fin (2 + rowsWork NI) → List Bool) (h0 : A (pubPort NI 0) = frame (r.input a))
    (hF : ∀ x : Fin (2 + rowsWork NI), 138 ≤ x.val → x.val < 148 → A x = [])
    (h5 : ∀ i : Fin 16, 3 ≤ i.val → i.val ≤ 6 → A (c5Port NI i) = [])
    (hS : ∀ x : Fin (2 + rowsWork NI), 2 + oB ≤ x.val → x.val < 2 + oB + needW a → A x = []) :
    ∃ A' : Fin (2 + rowsWork NI) → List Bool,
      Step (machine a NI oB) (cost a r) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ j : Fin 10, A' (wp NI (138 + j.val)) = symWord a ⟨j.val, by omega⟩ r) ∧
      (∀ i : Fin 16, 3 ≤ i.val → i.val ≤ 6 →
        A' (c5Port NI i) = frame (SignedSortKey.binary ((r.input a).length + 3) 0)) ∧
      (∀ x : Fin (2 + rowsWork NI), ¬ (138 ≤ x.val ∧ x.val < 148) → ¬ (2 + NI + 597 ≤ x.val ∧ x.val < 2 + NI + 601) →
        ¬ (2 + oB ≤ x.val ∧ x.val < 2 + oB + needW a) → A' x = A x) := by
  have hb := bd a NI oB hN
  have hi := sl_inj a NI oB hB hN
  have hW : needW a = (symVec a).extra + 1 := rfl
  have hn := hN
  unfold needW at hn hS
  obtain ⟨B, s1, b0, bj⟩ := vec_dock (symVec a) r (sl a NI oB) hi (fun _ => 0) A (fun _ => rfl)
    (by rw [show sl a NI oB ⟨0, by omega⟩ = pubPort NI 0 from Fin.ext (by rw [sl, vmap_val hb]; rfl), h0])
    (by
      intro j hj
      have hv : (sl a NI oB j).val = dst NI oB j.val := vmap_val hb j
      have hl := j.isLt
      unfold dst at hv
      rw [if_neg hj] at hv
      by_cases h10 : j.val ≤ 10
      · rw [if_pos h10] at hv
        exact hF _ (by omega) (by omega)
      · rw [if_neg h10] at hv
        by_cases h14 : j.val ≤ 14
        · rw [if_pos h14] at hv
          have e : sl a NI oB j = c5Port NI ⟨3 + (j.val - 11), by omega⟩ := Fin.ext (by rw [hv, c5_val]; simp only; omega)
          rw [e]
          exact h5 _ (by simp only; omega) (by simp only; omega)
        · rw [if_neg h14] at hv
          exact hS _ (by omega) (by omega))
  have key : ∀ j : Fin 14, B ⟨j.val + 1, by omega⟩ = symWord a j r := by
    intro j; fin_cases j <;> exact bj _ (by omega)
  refine ⟨_, s1, fun j => ?_, fun i h3 h6 => ?_, fun x hx1 hx2 hx3 => ?_⟩
  · have hj := j.isLt
    have hw : 138 + j.val < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hf : (wp NI (138 + j.val)).val = dst NI oB (j.val + 1) := by
      rw [wp_val hw]; unfold dst; rw [if_neg (by omega), if_pos (by omega)]; omega
    rw [sl, inst_at hb hi A B _ (j.val + 1) (by omega) hf]
    exact key ⟨j.val, by omega⟩
  · have hl := i.isLt
    have hf : (c5Port NI i).val = dst NI oB (i.val + 8) := by
      rw [c5_val]; unfold dst; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
    rw [sl, inst_at hb hi A B _ (i.val + 8) (by omega) hf]
    have := key ⟨i.val + 7, by omega⟩
    simp only [show i.val + 7 + 1 = i.val + 8 by omega] at this
    rw [this]
    have hi7 : 10 ≤ i.val + 7 := by omega
    have hi7' : i.val + 7 ≤ 13 := by omega
    obtain ⟨v, hv⟩ := i
    simp only at hi7 hi7' ⊢
    interval_cases v <;> rfl
  · by_cases hx0 : x.val = 0
    · have hf : x.val = dst NI oB 0 := by rw [hx0]; rfl
      rw [sl, inst_at hb hi A B _ 0 (by omega) hf, b0, show x = pubPort NI 0 from Fin.ext hx0, h0]
    · rw [sl]
      refine inst_off hb A B x (fun v hv h => ?_)
      unfold dst at h; split_ifs at h <;> omega

/-! ## 4. Consumer form at a SYM request -/

theorem flag_eq (n c : ℕ) : [decide (0 < n - c)] = [decide (c < n)] := by
  have : (0 < n - c) ↔ (c < n) := ⟨fun h => by omega, fun h => by omega⟩
  simp only [this]

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : ℕ)

/-- On a SYM request, words 0–8 ARE RC5's `symInit (sw) |circuits| (sbnd r)`. -/
theorem word_symInit (m : Fin 9) :
    symWord a ⟨m.val, by omega⟩ (.sym r four L target) =
      SymC5.symInit (SymC5.sw a r four L target) r.circuits.length (SymC5.sbnd r) m := by
  obtain ⟨m, hm⟩ := m
  interval_cases m
  · exact (RowsInit.BinWords.bin_word _ _ (SymC5.sbnd_lt a r four L target 0)).trans rfl
  · exact (RowsInit.BinWords.bin_word _ _ (SymC5.sbnd_lt a r four L target 1)).trans rfl
  · exact (RowsInit.BinWords.bin_word _ _ (SymC5.sbnd_lt a r four L target 2)).trans rfl
  · exact (RowsInit.BinWords.bin_word _ _ (SymC5.sbnd_lt a r four L target 3)).trans rfl
  · exact (flag_eq r.circuits.length 0).trans rfl
  · exact (flag_eq r.circuits.length 1).trans rfl
  · exact (flag_eq r.circuits.length 2).trans rfl
  · exact (flag_eq r.circuits.length 3).trans rfl
  · rfl

/-- **`SymC5Ready`** at RX's fixed indices (`iMode = 145`, `iniS m = 136+m`), for ANY bank that agrees with `words_run`'s exit on
the ports 138–147. -/
theorem sym_ready (NI : ℕ) (h : 146 ≤ NI) (A : Fin (2 + rowsWork NI) → List Bool)
    (hw : ∀ j : Fin 10, A (wp NI (138 + j.val)) = symWord a ⟨j.val, by omega⟩ (.sym r four L target)) :
    PartsStep.SymC5Ready a r four L target NI (fun i => A (initPort NI i)) (ThrInitReady.iMode NI h)
      (ThrInitReady.iniS NI h) := by
  refine ⟨?_, fun m => ?_⟩ <;> beta_reduce
  · rw [show initPort NI (ThrInitReady.iMode NI h) = wp NI (138 + 9) from ThrInitReady.pw NI _ _ rfl]
    exact hw ⟨9, by decide⟩
  · rw [show initPort NI (ThrInitReady.iniS NI h m) = wp NI (138 + m.val) from
      ThrInitReady.pw NI _ _ (by simp only [ThrInitReady.iniS]; omega)]
    exact (hw ⟨m.val, by omega⟩).trans (word_symInit a r four L target m)

end Sym

end
end RowsInit.FrameSymWords
