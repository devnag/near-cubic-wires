import Proof.Packets.PacketsCombineCost

/-! # P2 (ii)/(iii): the two combine stages, with capacity and cost DISCHARGED

Consumer: `RowPolySplitK.sym : SymCombineStageK Y K` and `RowPolySplitK.thr : ThrCombineStageK Y K`
(`Proof/Packets/PacketsRowPolySplitKit.lean`). Paper: the row's canonical polynomial expansion — SYM conjunction of
one-hot lookups, THR modular radix row (A.13.7, `paper.tex:3113-3142`) — charged once per row in `T_prep`
(`paper.tex:1197-1200`); budget class: source-polynomial (cost `≤ c·smallSize^d`, no table factor).

`symCombine`/`thrCombine` take only: the metadata machine (`SymMeta`/`ThrMeta`, typed in
`PacketsCombineSymLocal`/`PacketsCombineThrLocal`), the writer-reserve room `SymRoom X K`
(`8·commonReserve C w + 15 ≤ X.R`), and the scratch room in `Q2`/`Q3`. Capacity is `symCap`/`thrCap`
(proved for every `K`), cost is `sym_cost_le`/`thr_cost_le` below.
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
open Theorem25Completion.CycleBounds
noncomputable section

variable {a : DecompositionAlgorithm}

/-- The dominating coefficient and exponent of one stage's fuel inputs. -/
def costC (K : KitShape a) (mc : ℕ) : ℕ := mc + K.cC + K.cW + 65536 * (K.cC + 1) ^ 4 * K.cW ^ 8 + 1
def costD (K : KitShape a) (md : ℕ) : ℕ := md + 5 * K.dC + 9 * K.dW + 2

theorem reserve_poly (K : KitShape a) (r : Request) :
    commonReserve (K.C r) (K.w r) ≤ 65536 * (K.cC + 1) ^ 4 * K.cW ^ 8 * (r.smallSize a) ^ (4 * K.dC + 8 * K.dW) := by
  have hs := RCFive.PacketBounds.positive a r
  have hsC : 1 ≤ (r.smallSize a) ^ K.dC := Nat.one_le_pow _ _ hs
  have hC : K.C r + 1 ≤ (K.cC + 1) * (r.smallSize a) ^ K.dC := by
    have := K.C_le r; nlinarith
  have hW := K.w_le r
  have h4 : (K.C r + 1) ^ 4 ≤ ((K.cC + 1) * (r.smallSize a) ^ K.dC) ^ 4 := Nat.pow_le_pow_left hC 4
  have h8 : (2 ^ K.w r) ^ 8 ≤ (K.cW * (r.smallSize a) ^ K.dW) ^ 8 := Nat.pow_le_pow_left hW 8
  unfold commonReserve
  calc 65536 * (K.C r + 1) ^ 4 * 2 ^ (8 * K.w r)
      = 65536 * (K.C r + 1) ^ 4 * (2 ^ K.w r) ^ 8 := by rw [Nat.mul_comm 8, Nat.pow_mul]
    _ ≤ 65536 * ((K.cC + 1) * (r.smallSize a) ^ K.dC) ^ 4 * (K.cW * (r.smallSize a) ^ K.dW) ^ 8 := by gcongr
    _ = 65536 * (K.cC + 1) ^ 4 * K.cW ^ 8 * (r.smallSize a) ^ (4 * K.dC + 8 * K.dW) := by
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.pow_add]; ring

/-- One `Y` dominates every fuel input of a stage at request `r`. -/
theorem Y_le (K : KitShape a) (mc md mcost : ℕ) (r : Request)
    (hm : mcost ≤ mc * (r.smallSize a) ^ md) :
    mcost + K.C r + 2 ^ K.w r + commonReserve (K.C r) (K.w r) + r.smallSize a * r.smallSize a ≤
      costC K mc * (r.smallSize a) ^ costD K md := by
  have hs := RCFive.PacketBounds.positive a r
  have mono : ∀ e, e ≤ costD K md → (r.smallSize a) ^ e ≤ (r.smallSize a) ^ costD K md :=
    fun e he => Nat.pow_le_pow_right hs he
  have h1 : mcost ≤ mc * (r.smallSize a) ^ costD K md :=
    hm.trans (Nat.mul_le_mul_left _ (mono _ (by unfold costD; omega)))
  have h2 : K.C r ≤ K.cC * (r.smallSize a) ^ costD K md :=
    (K.C_le r).trans (Nat.mul_le_mul_left _ (mono _ (by unfold costD; omega)))
  have h3 : 2 ^ K.w r ≤ K.cW * (r.smallSize a) ^ costD K md :=
    (K.w_le r).trans (Nat.mul_le_mul_left _ (mono _ (by unfold costD; omega)))
  have h4 : commonReserve (K.C r) (K.w r) ≤ 65536 * (K.cC + 1) ^ 4 * K.cW ^ 8 * (r.smallSize a) ^ costD K md :=
    (reserve_poly K r).trans (Nat.mul_le_mul_left _ (mono _ (by unfold costD; omega)))
  have h5 : r.smallSize a * r.smallSize a ≤ 1 * (r.smallSize a) ^ costD K md := by
    rw [Nat.one_mul, ← Nat.pow_two]; exact mono _ (by unfold costD; omega)
  unfold costC
  nlinarith

theorem symN_le (r : Request) : symN r ≤ 4 := by
  cases r with
  | terminal => simp [symN]
  | sym r four L target => exact four
  | thr r four L target => simp [symN]

theorem symM_le (r : Request) : symM r ≤ r.smallSize a * r.smallSize a := by
  have hs := RCFive.PacketBounds.positive a r
  have hle : symM r ≤ r.smallSize a := by
    cases r with
    | terminal => simp [symM]
    | sym r four L target =>
      have hp := RCFive.PacketBounds.occurrence_power a (.sym r four L target)
      change ((symmetricFourfoldOccurrences r).length + 2) ^ _ ≤ _ at hp
      have := (Nat.le_self_pow (n := (Request.sym r four L target).degree a + 1) (by omega)
        ((symmetricFourfoldOccurrences r).length + 2)).trans hp
      show (symmetricFourfoldOccurrences r).length + 1 ≤ _
      omega
    | thr r four L target => simp [symM]
  exact hle.trans (Nat.le_mul_of_pos_left _ hs)

/-- **SYM fuel, a fixed power of `smallSize`.** -/
theorem sym_cost_le (K : KitShape a) (M : SymMeta a K) (r : Request) :
    symStageCost K M r ≤ 2 ^ 36 * (costC K M.coefficient + 1) ^ 26 * (r.smallSize a) ^ (26 * costD K M.degree) := by
  have hY := Y_le K M.coefficient M.degree (M.cost r) r (M.cost_le r)
  have h := symLocal_le (M.cost r) (K.C r) (K.w r) (symN r) (symM r)
    (M.cost r + K.C r + 2 ^ K.w r + commonReserve (K.C r) (K.w r) + r.smallSize a * r.smallSize a)
    (by generalize (2:ℕ) ^ K.w r = W; omega) (by generalize (2:ℕ) ^ K.w r = W; omega)
    (by generalize (2:ℕ) ^ K.w r = W; omega) (by generalize (2:ℕ) ^ K.w r = W; omega)
    (by have := symM_le (a := a) r; generalize (2:ℕ) ^ K.w r = W; omega) (symN_le r)
  exact h.trans (polyLe _ _ _ _ (RCFive.PacketBounds.positive a r) hY)

/-- **THR fuel, a fixed power of `smallSize`.** -/
theorem thr_cost_le (K : KitShape a) (M : ThrMeta a K) (r : Request) :
    thrStageCost K M r ≤ 2 ^ 36 * (costC K M.coefficient + 1) ^ 26 * (r.smallSize a) ^ (26 * costD K M.degree) := by
  have hs := RCFive.PacketBounds.positive a r
  have hY := Y_le K M.coefficient M.degree (M.cost r) r (M.cost_le r)
  have hss : r.smallSize a ≤ r.smallSize a * r.smallSize a := Nat.le_mul_of_pos_left _ hs
  have h := thrLocal_le (M.cost r) (K.C r) (K.w r) (thrKmax a r) (thrNmax a r)
    (M.cost r + K.C r + 2 ^ K.w r + commonReserve (K.C r) (K.w r) + r.smallSize a * r.smallSize a)
    (by generalize (2:ℕ) ^ K.w r = W; omega) (by generalize (2:ℕ) ^ K.w r = W; omega)
    (by generalize (2:ℕ) ^ K.w r = W; omega) (by generalize (2:ℕ) ^ K.w r = W; omega)
    (by unfold thrKmax; generalize (2:ℕ) ^ K.w r = W; omega) (by unfold thrNmax; generalize (2:ℕ) ^ K.w r = W; omega)
  exact h.trans (polyLe _ _ _ _ hs hY)

/-! ## The deliverables -/

/-- **(ii) The SYM combine stage** (the consumer's exact type). -/
def symCombine {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) (M : SymMeta a K)
    (hu : 106 + M.extra ≤ Y.u2) (room : SymRoom X K) : SymCombineStageK Y K :=
  symStage Y K M hu (symCap K) room (2 ^ 36 * (costC K M.coefficient + 1) ^ 26) (26 * costD K M.degree)
    (sym_cost_le K M)

/-- **(iii) The THR combine stage** — the modular radix row (the consumer's exact type). -/
def thrCombine {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) (M : ThrMeta a K)
    (hu : 107 + M.extra ≤ Y.u3) (room : SymRoom X K) : ThrCombineStageK Y K :=
  thrStage Y K M hu (thrCap K) room (2 ^ 36 * (costC K M.coefficient + 1) ^ 26) (26 * costD K M.degree)
    (thr_cost_le K M)

end
end NearCubicWires.PacketsCombine
