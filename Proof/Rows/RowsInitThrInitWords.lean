import Proof.Rows.RowsInitVecDock
import Proof.Rows.RowsInitBaseParams
import Proof.Packets.PacketsMetaCutoffStage

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.ThrInitWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta
open RowsConstruction RowsConstruction.BaseLayout RowsInit.LoopWords NearCubicWires.SupplierPipeline
noncomputable section

/-! ## 1. The new word stages -/

section Stages
variable (a : DecompositionAlgorithm)

theorem zeros_cost (x : ℕ) : RowsInit.LoopAux.zerosMap.cost x ≤ 2 * (x + 3) ^ 1 := by
  show 2 * x + 4 ≤ _
  rw [pow_one]
  omega

/-- `[true] = 1^1`. -/
def oneS : WordStage a (fun _ => [true]) := (constStage a 1).toWord

/-- `1^(12T+17)` (`w`, the base worker's result width minus 2). -/
def w17S : WordStage a (fun r => List.replicate (12 * (r.input a).length + 17) true) :=
  wofEq (affS a 12 5).toWord (fun r => by rw [val1]; ring_nf)

/-- `fb (12T+17) 0`. -/
def fbw0S : WordStage a (fun r => frame (SignedSortKey.binary (12 * (r.input a).length + 17) 0)) :=
  wofEq ((affS a 12 5).thenWordP zeroWordMap 8 1 zero_cost) (fun r => by rw [val1]; ring_nf)

/-- `1^(8(12T+17)+12)` (the base worker's `C`). -/
def cS : WordStage a (fun r => List.replicate (8 * (12 * (r.input a).length + 17) + 12) true) :=
  wofEq (affS a 96 52).toWord (fun r => by rw [val1]; ring_nf)

/-- `1^(12T+19)` (`wT`). -/
def wTS : WordStage a (fun r => List.replicate (12 * (r.input a).length + 19) true) :=
  wofEq (affS a 12 7).toWord (fun r => by rw [val1]; ring_nf)

/-- `fb T 0`. -/
def fbT0S : WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length 0)) :=
  (inputLenStage a).thenWordP zeroWordMap 8 1 zero_cost

/-- THR `F` as a unary stage (`Ff q T`, the traversal's `F`). -/
def fS : UnaryStage a (fun r => ThrBounds.FOf thrCF thrDF r.q (r.input a).length) :=
  ((qwS a).thenMapP (polyMap thrDF thrCF) (UnaryCalc.polyCoefficient thrDF thrCF) (thrDF+1)
    (poly_cost thrDF thrCF)).ofEq (fun r => by rw [val1, RowsInit.ThrParams.FOf_value]; congr 2)

/-- THR `U` as a unary stage (`Uf q T`, the traversal's `U`). -/
def uS : UnaryStage a (fun r => ThrBounds.UOf thrCU thrDU r.q (r.input a).length) :=
  ((qwS a).thenMapP (polyMap thrDU thrCU) (UnaryCalc.polyCoefficient thrDU thrCU) (thrDU+1)
    (poly_cost thrDU thrCU)).ofEq (fun r => by rw [val1, RowsInit.ThrParams.UOf_value]; congr 2)

/-- `0^(Ff q T + 1)`. -/
def f0S : WordStage a (fun r => List.replicate (ThrBounds.FOf thrCF thrDF r.q (r.input a).length + 1) false) :=
  ((fS a).thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)).thenWordP RowsInit.LoopAux.zerosMap 2 1 zeros_cost

/-- `0^(Uf q T + 1)`. -/
def u0S : WordStage a (fun r => List.replicate (ThrBounds.UOf thrCU thrDU r.q (r.input a).length + 1) false) :=
  ((uS a).thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)).thenWordP RowsInit.LoopAux.zerosMap 2 1 zeros_cost

/-- The prime reserve, for every request: `16384·(T + cutoffOf r + 1)^3` (`= PrimeReserve.rpOf a` on THR). -/
def rpVal (r : Request) : ℕ := UnaryCalc.value 3 16384 ((r.input a).length + cutoffOf a r)

def rpS : WordStage a (fun r => List.replicate (rpVal a r) true) :=
  (((inputLenStage a).pairP (NearCubicWires.PacketsMeta.cutoffStage a) addMap2 6 1 add_cost).thenMapP
    (polyMap 3 16384) (UnaryCalc.polyCoefficient 3 16384) (3+1) (poly_cost 3 16384)).toWord

/-- The base worker's `U` at explicit constants: `UOf' cD dD cU dU T = cU·(mB + cD·(mB+1)^dD + 1)^dU`, `mB = 100T+200`. -/
def bUS (cD dD cU dU : ℕ) : WordStage a (fun r => List.replicate (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length) true) :=
  wofEq (((affS a 100 100).pairP ((affS a 100 100).thenMapP (polyMap dD cD) (UnaryCalc.polyCoefficient dD cD) (dD+1)
    (poly_cost dD cD)) addMap2 6 1 add_cost).thenMapP (polyMap dU cU) (UnaryCalc.polyCoefficient dU cU) (dU+1)
    (poly_cost dU cU)).toWord (fun r => by
      simp only [UnaryCalc.value, ThrBaseBounds.UOf', ThrBaseBounds.DOf, ThrBaseBounds.mBOf]
      ring_nf)

end Stages

/-! ## 2. The 31 words -/

def thrInitWord (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ) (cD dD cU dU : ℕ) (j : Fin 31)
    (r : Request) : List Bool :=
  let T := (r.input a).length
  match j.val with
  | 0 => List.replicate (12 * T + 19) true
  | 1 => [true]
  | 2 => frame (SignedSortKey.binary T (bnd r 0))
  | 3 => frame (SignedSortKey.binary T (bnd r 1))
  | 4 => frame (SignedSortKey.binary T (bnd r 2))
  | 5 => frame (SignedSortKey.binary T (bnd r 3))
  | 6 => List.replicate (12 * T + 17) true
  | 7 => frame (SignedSortKey.binary (12 * T + 17) 0)
  | 8 => List.replicate (8 * (12 * T + 17) + 12) true
  | 9 => RepairSource.VerifierDecoding.CompareMachine.word 0
  | 10 => List.replicate (12 * T + 19) true
  | 11 => frame (r.topWord a)
  | 12 => List.replicate T true
  | 13 => frame (SignedSortKey.binary (12 * T + 19) 0)
  | 14 => frame (SignedSortKey.binary (12 * T + 19) 0)
  | 15 => frame (SignedSortKey.binary (12 * T + 19) 1)
  | 16 => frame (SignedSortKey.binary T 0)
  | 17 => frame (SignedSortKey.binary T 0)
  | 18 => List.replicate (ThrBounds.FOf thrCF thrDF r.q T) true
  | 19 => List.replicate (ThrBounds.FOf thrCF thrDF r.q T + 1) false
  | 20 => List.replicate (ThrBounds.UOf thrCU thrDU r.q T) true
  | 21 => List.replicate (ThrBounds.UOf thrCU thrDU r.q T + 1) false
  | 22 => List.replicate (rpVal a r) true
  | 23 => List.replicate (ThrBaseBounds.UOf' cD dD cU dU T) true
  | 24 => RepairSource.VerifierDecoding.CompareMachine.word 0
  | 25 => RepairSource.VerifierDecoding.CompareMachine.word 1
  | 26 => RepairSource.VerifierDecoding.CompareMachine.word 2
  | 27 => RepairSource.VerifierDecoding.CompareMachine.word 3
  | 28 => frame (SignedSortKey.binary (12 * T + 19) 1)
  | 29 => UnaryTemplate.tape (RowsInit.LoopFan.circOf r)
  | 30 => [true]
  | _ => []

/-- **The 31 words by ONE fixed machine** (the `snoc` chain; `bndW c` the cascade-bound word stages). -/
def initVec (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
    (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))
    (cD dD cU dU : ℕ) :=
  ((((((((((((((((((((((((((((((((VecStage.nil a (fun _ _ => [])).snoc (wTS a)).snoc (oneS a)).snoc (bndW 0)).snoc (bndW
    1)).snoc (bndW 2)).snoc (bndW 3)).snoc (w17S a)).snoc (fbw0S a)).snoc (cS a)).snoc (w4 a)).snoc (wTS a)).snoc (w22
    a)).snoc (w21 a)).snoc (w11 a)).snoc (w11 a)).snoc (w13 a)).snoc (fbT0S a)).snoc (fbT0S a)).snoc (w15 a)).snoc
    (f0S a)).snoc (w14 a)).snoc (u0S a)).snoc (rpS a)).snoc (bUS a cD dD cU dU)).snoc (w4 a)).snoc (w16 a)).snoc (w17
    a)).snoc (w18 a)).snoc (w13 a)).snoc (w20 a)).snoc (oneS a))

end
end RowsInit.ThrInitWords
