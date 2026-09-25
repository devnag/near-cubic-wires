import Proof.Packets.PacketsCircBound
import Proof.Rows.RowsInitBinWords
import Proof.Rows.RowsSymLoopFan

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

namespace RowsInit.SymLoopWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.SupplierPipeline
open RowsConstruction RowsConstruction.BaseLayout RowsInit.SymLoopFan
noncomputable section

/-! ## 1. The SYM driver lengths `driverLen r c` (`c < 4`) -/

/-- Circuit `i`'s prefix-sum term is its gate count plus one. -/
theorem getD_succ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (i : ℕ) (hi : i < r.circuits.length) :
    (r.circuits.map (fun c => c.bottomCount + 1)).getD i 0 = SymMeaning.gateCount r i + 1 := by
  simp [SymMeaning.gateCount, SymMeaning.symGates, List.getD_eq_getElem?_getD, hi]

/-- **The value identity**: `(symPre (c+1) − 1)·[c < #circuits]` is the SYM driver length (`0` off SYM). -/
theorem dl_eq (c : ℕ) (r : Request) :
    (NearCubicWires.PacketsConstruction.CircBound.symPre (c + 1) r - 1) *
        (if (if NearCubicWires.PacketsKeys.Native.nCirc r - c = 0 then 1 else 0) = 0 then 1 else 0) = dlv c r := by
  cases r with
  | terminal => simp [NearCubicWires.PacketsConstruction.CircBound.symPre, dlv]
  | thr r four L tg => simp [NearCubicWires.PacketsConstruction.CircBound.symPre, dlv]
  | sym r four L tg =>
    by_cases hc : c < r.circuits.length
    · have h1 : r.circuits.length - c ≠ 0 := by omega
      have e1 : (if (if NearCubicWires.PacketsKeys.Native.nCirc (Request.sym r four L tg) - c = 0 then 1 else 0) = 0
          then 1 else 0) = 1 := by
        simp [NearCubicWires.PacketsKeys.Native.nCirc, h1]
      rw [e1, Nat.mul_one]
      show ((r.circuits.take (c + 1)).map (fun c => c.bottomCount + 1)).sum - 1 = SymMeaning.driverLen r c
      unfold SymMeaning.driverLen
      rw [if_pos hc, SymMeaning.map_take_sum, Finset.sum_range_succ, getD_succ r c hc]
      have e : ∑ i ∈ Finset.range c, (r.circuits.map (fun c => c.bottomCount + 1)).getD i 0 =
          ∑ i ∈ Finset.range c, (SymMeaning.gateCount r i + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact getD_succ r i (by have := Finset.mem_range.mp hi; omega)
      rw [e]
      omega
    · have h1 : r.circuits.length - c = 0 := by omega
      have e1 : (if (if NearCubicWires.PacketsKeys.Native.nCirc (Request.sym r four L tg) - c = 0 then 1 else 0) = 0
          then 1 else 0) = 0 := by
        simp [NearCubicWires.PacketsKeys.Native.nCirc, h1]
      rw [e1, Nat.mul_zero]
      show 0 = SymMeaning.driverLen r c
      unfold SymMeaning.driverLen
      rw [if_neg hc]

section Words
variable (a : DecompositionAlgorithm)

/-- `symPre (c+1) − 1`. -/
def predS (c : ℕ) (hc : c < 4) :
    UnaryStage a (fun r => NearCubicWires.PacketsConstruction.CircBound.symPre (c + 1) r - 1) :=
  (NearCubicWires.PacketsConstruction.CircBound.symPreStage a (c + 1) (by omega)).pairP
    (NearCubicWires.PacketsConstruction.CircBound.constS a 1) NearCubicWires.PacketsConstruction.CircBound.monusMap2 6 1
    NearCubicWires.PacketsConstruction.CircBound.monus_cost

/-- `[c < #circuits]`. -/
def indS (c : ℕ) :
    UnaryStage a (fun r => if (if NearCubicWires.PacketsKeys.Native.nCirc r - c = 0 then 1 else 0) = 0 then 1 else 0) :=
  (NearCubicWires.PacketsConstruction.CircBound.indStage a c).thenMapP isZeroMap 4 1 isZero_cost

/-- **The SYM driver length of slot `c`** (`SymMeaning.driverLen r c` on SYM requests, `0` otherwise). -/
def dlS (c : ℕ) (hc : c < 4) : UnaryStage a (dlv c) :=
  ((predS a c hc).pairP (indS a c) mulMap2 8 2 mul_cost).ofEq (fun r => dl_eq c r)

/-- **`word (driverLen r c)`** (POOL-3's SYM request stage). -/
def dlW (c : ℕ) (hc : c < 4) : WordStage a (fun r => RepairSource.VerifierDecoding.CompareMachine.word (dlv c r)) :=
  (dlS a c hc).thenWordP cmpWordMap 6 1 cmp_cost

/-- `T+3`, `T = |input|`. -/
def t3S : UnaryStage a (fun r => (r.input a).length + 3) :=
  (inputLenStage a).thenMapP (plusMap 3) (2 * 3 + 4) 1 (plus_cost 3)

theorem four_lt (T : ℕ) : 4 < 2 ^ (T + 3) :=
  Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ T + 3))

def x10 : WordStage a (fun r => frame (SignedSortKey.binary ((r.input a).length + 3) 0)) :=
  (t3S a).thenWordP zeroWordMap 8 1 zero_cost
def x15 : WordStage a (fun _ => RepairSource.VerifierDecoding.CompareMachine.word 4) :=
  (RowsInit.LoopWords.constStage a 4).thenWordP cmpWordMap 6 1 cmp_cost
def x16 : WordStage a (fun r => frame (SignedSortKey.binary ((r.input a).length + 3) 4)) :=
  RowsInit.BinWords.binWordS (t3S a) (RowsInit.LoopWords.constStage a 4) (fun r => four_lt (r.input a).length)
def xR : WordStage a (fun r => List.replicate (symRes r.q (r.input a).length) true) :=
  ((qStage a).pairP (inputLenStage a) addMap2 6 1 add_cost).thenMapP (RowsInit.LoopWords.polyMap symRd (symRc+1))
    (UnaryCalc.polyCoefficient symRd (symRc+1)) (symRd+1) (RowsInit.LoopWords.poly_cost symRd (symRc+1)) |>.toWord

end Words

/-! ## 2. The vector stage: all 18 words in one fixed machine -/

/-- **The SYM loop block's request-level words**: the 17 fanout sources on tapes 1..17, `1^R` on tape 18. -/
def symVec (a : DecompositionAlgorithm) :=
  ((((((((((((((((((VecStage.nil a (fun _ _ => [])).snoc (RowsInit.LoopWords.w0 a)).snoc (RowsInit.LoopWords.w1 a)).snoc
    (RowsInit.LoopWords.w2 a)).snoc (RowsInit.LoopWords.w3 a)).snoc (RowsInit.LoopWords.w4 a)).snoc
    (RowsInit.LoopWords.w5 a)).snoc (RowsInit.LoopWords.w6 a)).snoc (RowsInit.LoopWords.w7 a)).snoc
    (RowsInit.LoopWords.w8 a)).snoc (RowsInit.LoopWords.w9 a)).snoc (x10 a)).snoc (dlW a 0 (by omega))).snoc
    (dlW a 1 (by omega))).snoc (dlW a 2 (by omega))).snoc (dlW a 3 (by omega))).snoc (x15 a)).snoc (x16 a)).snoc (xR a)

theorem vec_cost_le (a : DecompositionAlgorithm) (r : Request) :
    (symVec a).cost r ≤ (symVec a).coefficient * (r.smallSize a) ^ (symVec a).degree :=
  (symVec a).cost_le r

end
end RowsInit.SymLoopWords
