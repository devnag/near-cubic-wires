import Proof.Packets.PacketsCombineTabWriter
import Proof.Packets.PacketsCombineThrLocal

/-! # P2 (iii) table writer, part 8: the writer at a THR key = `ThrMeta`'s tape 15, and its cost

Consumer: `ThrMeta a K` (`Proof/Packets/PacketsCombineThrLocal.lean`), field `run`, tape 15:
`A ⟨15, _⟩ = thrTableOf r L target k`, `H ⟨15, _⟩ = N * (thrD k * (pop+1) + 1)`, `N = (pop+1)^(thrD k)`,
`pop = (thresholdFourfoldOccurrences r).length`. Paper: A.13.7 (`paper.tex:3113-3142`), internal preprocessing in
`T_prep` (`paper.tex:1197-1200`); budget class source-polynomial: `writerCost ≤ 2^20 · (S+1)^4` with
`S = pop + D + p + res + N` (each summand `≤ poly(smallSize)`: `N ≤ tupleWork`, `p ≤ primeCutoff`, `res < p`).

`writer_thr`: the one fixed machine `writerM` (12 local tapes), docked by the `ThrMeta` assembler with inputs
reading as `word pop`, `word D`, `word (D*(pop+1))`, `word prime`, `word residue`, `word N` (e.g. the templates
`ThrMeta` already writes on its tapes 12, 13 (`K`) and 14 (`N`)), writes EXACTLY the consumer's tape-15 table
with the consumer's head position; inputs and their heads are returned unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
open Tab
noncomputable section

/-- **The table writer at a THR key writes `ThrMeta`'s tape 15.** -/
theorem writer_thr {a : DecompositionAlgorithm} (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) (Pop Dw KW Pw RSw Nw : List Bool)
    (hPop : ReadsWord Pop (thresholdFourfoldOccurrences r).length) (hDw : ReadsWord Dw (thrD k))
    (hKW : ReadsWord KW (thrD k * ((thresholdFourfoldOccurrences r).length + 1)))
    (hPw : ReadsWord Pw k.prime.val) (hRS : ReadsWord RSw k.residue.val)
    (hNw : ReadsWord Nw (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k)) :
    ∃ (H' : Fin 12 → ℕ) (A' : Fin 12 → List Bool),
      Step writerM (writerCost (thresholdFourfoldOccurrences r).length (thrD k) k.prime.val k.residue.val
          (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k))
        (fun _ => 0) (wIn Pop Dw KW Pw RSw Nw) H' A' ∧
      (∀ i : Fin 12, i.val < 6 → A' i = wIn Pop Dw KW Pw RSw Nw i ∧ H' i = 0) ∧
      A' 10 = thrTableOf r L target k ∧
      H' 10 = ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k *
        (thrD k * ((thresholdFourfoldOccurrences r).length + 1) + 1) := by
  have hp : 1 ≤ k.prime.val := by have := k.residue.isLt; omega
  obtain ⟨H', A', st, hin, hout, hhead⟩ := writer_run (thresholdFourfoldOccurrences r).length (thrD k) k.prime.val
    k.residue.val (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k) hp Pop Dw KW Pw RSw Nw hPop hDw hKW hPw
    hRS hNw
  refine ⟨H', A', st, hin, ?_, ?_⟩
  · rw [hout, thrTableOf, tabPrefix_full]
  · rw [hhead, tabPrefix_length]

/-! ## The cost, as one fixed polynomial -/

theorem writerCost_mono (pop D p res N S : ℕ) (h1 : pop ≤ S) (h2 : D ≤ S) (h3 : p ≤ S) (h4 : res ≤ S) (h5 : N ≤ S) :
    writerCost pop D p res N ≤ writerCost S S S S S := by
  unfold writerCost genCost ucopyCost Tab.loopCost rowCost hornerBlock odoBudget
  gcongr

theorem writerCost_diag (S : ℕ) : writerCost S S S S S ≤ 2 ^ 20 * (S + 1) ^ 4 := by
  refine (writerCost_mono S S S S S (S + 1) (by omega) (by omega) (by omega) (by omega) (by omega)).trans ?_
  unfold writerCost genCost ucopyCost Tab.loopCost rowCost hornerBlock odoBudget
  simp only [Nat.add_sub_cancel]
  ring_nf
  nlinarith [Nat.zero_le (S ^ 2), Nat.zero_le (S ^ 3), Nat.zero_le (S ^ 4), Nat.zero_le S]

/-- **The table writer's cost is one fixed polynomial** of `S = pop + D + p + res + N`. -/
theorem writerCost_le (pop D p res N : ℕ) :
    writerCost pop D p res N ≤ 2 ^ 20 * (pop + D + p + res + N + 1) ^ 4 :=
  (writerCost_mono pop D p res N (pop + D + p + res + N) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (writerCost_diag _)

end

end NearCubicWires.PacketsCombine

