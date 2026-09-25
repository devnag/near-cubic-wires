import Proof.Packets.PacketsFieldWidth
import Proof.Packets.PacketsMetaMul

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsMeta
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## Role rewriting -/

theorem lr_src {t s W : ℕ} {P : Machine t s} {n : ℕ} {σ σ' τ : Fin t → TS} (h : LRuns W P n σ τ)
    (e : σ = σ') : LRuns W P n σ' τ := e ▸ h

/-! ## The unary output loop -/

namespace Emit

/-- Tapes: 0 ruler, 1 zero register, 2 the value `V`, 3 flag, 4 the unary output. -/
def test := swAt subF false false (0 : Fin 5) 1 2 3

def body := Composition.machine (swAt subF true true (0 : Fin 5) 2 1 3) (RecoveryFocus.machine ![(4 : Fin 5)] append)

def machine := Loop test body (3 : Fin 5)

def st (V n0 i : ℕ) (b : Bool) : Fin 5 → TS := ![.ruler, .reg 0, .reg (V - i), .flag b, .out (n0 + i)]

theorem test_run (W V n0 i : ℕ) (b : Bool) (hi : i ≤ V) (hV : V < 2 ^ W) :
    LRuns W test (2 * W + 3) (st V n0 i b) (st V n0 i (decide (i < V))) := by
  have h := lt_at (W := W) (st V n0 i b) (0 : Fin 5) 1 2 3 (by decide) 0 (V - i) b rfl rfl rfl rfl
    (Nat.two_pow_pos W) (by omega)
  refine h.congr_out ?_
  have e : decide (0 < V - i) = decide (i < V) := by
    by_cases h : i < V
    · simp [h]
    · simp [h]
  rw [e]
  funext j; fin_cases j <;> rfl

theorem body_run (W V n0 i : ℕ) (hi : i < V) (hV : V < 2 ^ W) :
    LRuns W body (2 * W + 3 + 1 + 1) (st V n0 i true) (st V n0 (i + 1) false) := by
  have h1 := dec_at (W := W) (st V n0 i true) (0 : Fin 5) 2 1 3 (by decide) (V - i) 0 true rfl rfl rfl rfl rfl
    (by omega) (by omega)
  have h2 := (append_lruns W (n0 + i)).dockK ![(4 : Fin 5)] (by decide)
    (Function.update (Function.update (st V n0 i true) 2 (.reg (V - i - 1))) 3 (.flag false))
    (by intro j; fin_cases j; rfl) [0] (by intro j hj; fin_cases j; simp at hj)
  refine (h1.seq h2).congr_out ?_
  funext j; fin_cases j
  · rfl
  · rfl
  · exact congrArg TS.reg (by omega)
  · rfl
  · exact congrArg TS.out (by omega)

/-- **The output loop.** -/
theorem run (W V n0 : ℕ) (b : Bool) (hV : V < 2 ^ W) :
    LRuns W machine ((V + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2))
      ![.ruler, .reg 0, .reg V, .flag b, .out n0] ![.ruler, .reg 0, .reg 0, .flag false, .out (n0 + V)] := by
  have h := Loop.runs test body (3 : Fin 5) (fun i => st V n0 i (if i = 0 then b else false))
    (fun i => st V n0 i (decide (i < V))) V
    (fun i hi => test_run W V n0 i _ hi hV) (fun i _ => rfl)
    (fun i hi => by
      have hb := body_run W V n0 i hi hV
      have e1 : decide (i < V) = true := by simp [hi]
      have e2 : (if i + 1 = 0 then b else false) = false := by simp
      rw [e1, e2]
      exact hb)
  refine lr_src (h.congr_out ?_) ?_
  · funext j; fin_cases j
    · rfl
    · rfl
    · exact congrArg TS.reg (by omega)
    · simp [st]
    · rfl
  · funext j; fin_cases j <;> simp [st]

end Emit

/-! ## Setup: unframe the field, build the ruler -/

namespace Setup

/-- The field tape's content. -/
def ff (w : List Bool) : ℕ → Bool := fun j => readTapeBit (RepairOrdinary.frame w) j

/-- Marks of a stream. -/
def mk (w : List Bool) : ℕ → Bool := sf (List.replicate w.length true)

/-- Tapes: 0 the framed field, 1 stream, 2 marks, 3 ruler. -/
def machine (k : ℕ) :=
  Composition.machine (RecoveryFocus.machine ![(0 : Fin 4), 1, 2] Unframe.machine)
    (Composition.machine (RecoveryFocus.machine ![(3 : Fin 4)] moveR)
      (Composition.machine (RecoveryFocus.machine ![(2 : Fin 4), 1, 3] (Ruler.append k))
        (RecoveryFocus.machine ![(3 : Fin 4)] Ruler.finish)))

def cost (k n : ℕ) : ℕ := (5 * n + 10) + 1 + (1 + 1 + (((k + 1) * n + n + 7) + 1 + (k * n + 3)))

theorem rb_one : Ruler.rb 1 = blank := by
  funext j; simp [Ruler.rb, blank]; omega

/-- **Setup.** The stream holds the field at cursor `1`, the ruler has width `k·|w|`. -/
theorem run (k : ℕ) (hk : 1 ≤ k) (w : List Bool) :
    LRuns (k * w.length) (machine k) (cost k w.length)
      ![.cells (ff w) 0, .cells blank 0, .cells blank 0, .cells blank 0]
      ![.cells (ff w) (RepairOrdinary.frame w).length, .cells (sf w) 1, .cells (mk w) 1, .ruler] := by
  set W := k * w.length with hW
  have h1 := (Unframe.lruns W 0 w (ff w) (fun i _ => by simp [ff, readTapeBit])).dockK ![(0 : Fin 4), 1, 2]
    (by decide) (![.cells (ff w) 0, .cells blank 0, .cells blank 0, .cells blank 0] : Fin 4 → TS)
    (by intro j; fin_cases j <;> rfl) [0, 1, 2] (by intro j hj; fin_cases j <;> simp at hj)
  have h2 := (moveR_lruns W 0 blank).dockK ![(3 : Fin 4)] (by decide)
    (![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1, .cells blank 0] :
      Fin 4 → TS) (by intro j; fin_cases j; rfl) [0] (by intro j hj; fin_cases j; simp at hj)
  have h3 := (Ruler.append_lruns W k hk w.length 1 le_rfl (sf w)).dockK ![(2 : Fin 4), 1, 3] (by decide)
    (![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1,
      .cells (Ruler.rb 1) 1] : Fin 4 → TS) (by intro j; fin_cases j <;> rfl) [2]
    (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have h4 := (Ruler.finish_lruns W).dockK ![(3 : Fin 4)] (by decide)
    (![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1,
      .cells (Ruler.rb (W + 1)) (W + 1)] : Fin 4 → TS) (by intro j; fin_cases j; rfl) [0]
    (by intro j hj; fin_cases j; simp at hj)
  have e1 : ([0, 1, 2] : List (Fin 3)).foldr (fun j ρ => Function.update ρ ((![(0 : Fin 4), 1, 2] : Fin 3 → Fin 4) j)
      ((![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1,
        .cells (sf (List.replicate w.length true)) 1] : Fin 3 → TS) j))
      (![.cells (ff w) 0, .cells blank 0, .cells blank 0, .cells blank 0] : Fin 4 → TS) =
      ![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1, .cells blank 0] := by
    funext j; fin_cases j <;> rfl
  have e2 : ([0] : List (Fin 1)).foldr (fun j ρ => Function.update ρ ((![(3 : Fin 4)] : Fin 1 → Fin 4) j)
      ((![.cells blank (0 + 1)] : Fin 1 → TS) j))
      (![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1, .cells blank 0] :
        Fin 4 → TS) =
      ![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1,
        .cells (Ruler.rb 1) 1] := by
    rw [rb_one]; funext j; fin_cases j <;> rfl
  have e3 : ([2] : List (Fin 3)).foldr (fun j ρ => Function.update ρ ((![(2 : Fin 4), 1, 3] : Fin 3 → Fin 4) j)
      ((![.cells (sf (List.replicate w.length true)) 1, .cells (sf w) 1,
        .cells (Ruler.rb (1 + k * w.length)) (1 + k * w.length)] : Fin 3 → TS) j))
      (![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1,
        .cells (Ruler.rb 1) 1] : Fin 4 → TS) =
      ![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1,
        .cells (Ruler.rb (W + 1)) (W + 1)] := by
    rw [hW, Nat.add_comm 1 (k * w.length)]; funext j; fin_cases j <;> rfl
  have e4 : ([0] : List (Fin 1)).foldr (fun j ρ => Function.update ρ ((![(3 : Fin 4)] : Fin 1 → Fin 4) j)
      ((![.ruler] : Fin 1 → TS) j))
      (![.cells (ff w) (0 + (RepairOrdinary.frame w).length), .cells (sf w) 1, .cells (mk w) 1,
        .cells (Ruler.rb (W + 1)) (W + 1)] : Fin 4 → TS) =
      ![.cells (ff w) (RepairOrdinary.frame w).length, .cells (sf w) 1, .cells (mk w) 1, .ruler] := by
    rw [Nat.zero_add]; funext j; fin_cases j <;> rfl
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  exact h1.seq (h2.seq (h3.seq h4))

end Setup

/-! ## A register program on one field is a `UnaryStage` -/

/-- The entry roles of a scanner on the field `F`: the framed field on tape 0 (head 0), the empty output on
tape 1, every other tape blank. -/
def initRoles (t : ℕ) (F : List Bool) : Fin t → TS := fun i =>
  if i.val = 0 then .cells (Setup.ff F) 0 else if i.val = 1 then .out 0 else .cells blank 0

theorem init_TR (W e : ℕ) (F : List Bool) (i : Fin (2 + e)) :
    TR W (initRoles (2 + e) F i) ((fun _ => 0) i) (scanIn e (RepairOrdinary.frame F) i) := by
  unfold initRoles scanIn
  by_cases h0 : i.val = 0
  · simp only [h0, if_true]
    exact ⟨rfl, fun j => rfl⟩
  · by_cases h1 : i.val = 1
    · simp only [h0, h1, if_true, if_false]
      exact ⟨rfl, rfl⟩
    · simp only [h0, h1, if_false]
      exact ⟨rfl, fun j => by simp [readTapeBit, blank]⟩

/-- **The adapter.** One fixed register program `P` on the scanner of field `j`, whose run ends with
`.out (v r)` on tape 1 within `n r ≤ c·smallSize^d` steps, is one `UnaryStage a v`. -/
def scanStage (a : DecompositionAlgorithm) (j : Fin 5) (v : Request → ℕ) {e s : ℕ} (P : Machine (2 + e) s)
    (W n : Request → ℕ) (c d : ℕ)
    (hrun : ∀ r, ∃ σ' : Fin (2 + e) → TS, LRuns (W r) P (n r) (initRoles (2 + e) (fields a r j)) σ' ∧
      σ' ⟨1, by omega⟩ = .out (v r))
    (hcost : ∀ r, n r ≤ c * (r.smallSize a) ^ d) : UnaryStage a v where
  extra := 13 + e + 1
  states := _
  machine := fieldMachineE P j
  cost := fun r => 6 * (r.input a).length + 17 + 1 + (2 * n r + 2)
  coefficient := 2 * c + 26
  degree := d + 1
  cost_le := by
    intro r
    have h1 := input_le_small a r
    have h2 := hcost r
    have hs : 1 ≤ r.smallSize a := one_le_small a r
    have p1 : r.smallSize a ≤ (r.smallSize a) ^ (d + 1) := Nat.le_self_pow (by omega) _
    have p2 : (r.smallSize a) ^ d ≤ (r.smallSize a) ^ (d + 1) := pow_mono_small a r d 1
    have p0 : 1 ≤ (r.smallSize a) ^ (d + 1) := Nat.one_le_pow _ _ hs
    have e : (2 * c + 26) * (r.smallSize a) ^ (d + 1) =
        2 * (c * (r.smallSize a) ^ (d + 1)) + 26 * (r.smallSize a) ^ (d + 1) := by ring
    have hc : c * (r.smallSize a) ^ d ≤ c * (r.smallSize a) ^ (d + 1) := Nat.mul_le_mul_left c p2
    rw [e]
    omega
  run := by
    intro r
    obtain ⟨σ', hl, hv⟩ := hrun r
    obtain ⟨H1, A1, hs, hA⟩ := hl (fun _ => 0) (scanIn e (RepairOrdinary.frame (fields a r j)))
      (init_TR (W r) e (fields a r j))
    have h1 := hA ⟨1, by omega⟩
    rw [hv] at h1
    exact field_runE P j a r (v r) (n r) H1 A1 hs h1.2

end
end NearCubicWires.PacketsKeys

