import Proof.Packets.PacketsSymMaskProg

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsSymBits.Win
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.PacketsMeta NearCubicWires.PacketsSymBits
noncomputable section

/-- A unary word `1^v` read from cell `0`, cursor `h`. -/
def uw (v h : ℕ) : TS := .cells (fun i => decide (i < v)) h

theorem read_rep (v i : ℕ) : readTapeBit (List.replicate v true) i = decide (i < v) := by
  unfold readTapeBit
  by_cases h : i < v
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]; simp [h]

/-- The window: `P` bits of `top` from position `off`, `false` past its end. -/
def win (top : List Bool) (off P : ℕ) : List Bool := List.ofFn (fun i : Fin P => sf top (1 + off + i.val))

theorem win_take_succ (top : List Bool) (off P i : ℕ) (hi : i < P) :
    (win top off P).take (i + 1) = (win top off P).take i ++ [sf top (1 + off + i)] := by
  rw [List.take_succ_eq_append_getElem (by simp [win]; exact hi)]
  simp [win]

theorem win_take_all (top : List Bool) (off P : ℕ) : (win top off P).take P = win top off P :=
  List.take_of_length_le (by simp [win])

/-! ## The machines -/

def unfL := RecoveryFocus.machine ![(0 : Fin 9), 1, 2] Unframe.machine
def peekOff := RecoveryFocus.machine ![(3 : Fin 9), 7] peek
def moveT := RecoveryFocus.machine ![(1 : Fin 9)] moveR
def moveOff := RecoveryFocus.machine ![(3 : Fin 9)] moveR
def skipL := Loop peekOff (Composition.machine moveT moveOff) (7 : Fin 9)
def peekLen := RecoveryFocus.machine ![(4 : Fin 9), 7] peek
def peekT := RecoveryFocus.machine ![(1 : Fin 9), 8] peek
def appB (b : Bool) := RecoveryFocus.machine ![(5 : Fin 9), 6] (sapp b)
def moveLen := RecoveryFocus.machine ![(4 : Fin 9)] moveR
def copyBody := Composition.machine peekT
  (Composition.machine (Ite (nop 9) (appB true) (appB false) (8 : Fin 9)) (Composition.machine moveT moveLen))
def copyL := Loop peekLen copyBody (7 : Fin 9)

/-- **The window tail.** -/
def tailL := Composition.machine unfL (Composition.machine skipL copyL)

def tailCost (m off P : ℕ) : ℕ :=
  (5 * m + 10) + 1 + ((off + 1) * (1 + (1 + 1 + 1) + 2) + 1 + (P + 1) * (1 + (1 + 1 + (0 + 1 + 1 + 2 + 1 + (1 + 1 + 1))) + 2))

/-! ## The runs -/

section Runs
variable (W : ℕ) (fx : ℕ → Bool) (h : ℕ) (top : List Bool) (off P : ℕ) (o : List Bool) (f1 f2 : Bool)

/-- The roles after the unframe. -/
def st0 : Fin 9 → TS := ![.cells fx (h + (frame top).length), .cells (sf top) 1,
  .cells (sf (List.replicate top.length true)) 1, uw off 0, uw P 0, sS o, sM o, .flag f1, .flag f2]

theorem unf_run (hX : ∀ i, i < (frame top).length → fx (h + i) = (frame top).getD i false) :
    LRuns W unfL (5 * top.length + 10)
      ![.cells fx h, .cells PacketsMeta.blank 0, .cells PacketsMeta.blank 0, uw off 0, uw P 0, sS o, sM o, .flag f1, .flag f2]
      (st0 fx h top off P o f1 f2) := by
  have hl := (Unframe.lruns W h top fx hX).dockK ![(0 : Fin 9), 1, 2] (by decide)
    ![.cells fx h, .cells PacketsMeta.blank 0, .cells PacketsMeta.blank 0, uw off 0, uw P 0, sS o, sM o, .flag f1, .flag f2]
    (by intro j; fin_cases j <;> rfl) [0, 1, 2] (by intro j hj; fin_cases j <;> simp at hj)
  refine hl.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- The skip loop's states. -/
def sk (i : ℕ) (b : Bool) : Fin 9 → TS := ![.cells fx (h + (frame top).length), .cells (sf top) (1 + i),
  .cells (sf (List.replicate top.length true)) 1, uw off i, uw P 0, sS o, sM o, .flag b, .flag f2]

theorem skip_run : LRuns W skipL ((off + 1) * (1 + (1 + 1 + 1) + 2)) (st0 fx h top off P o f1 f2)
    (sk fx h top off P o f2 off false) := by
  have hl := Loop.runs (W := W) peekOff (Composition.machine moveT moveOff) (7 : Fin 9)
    (fun i => sk fx h top off P o f2 i (if i = 0 then f1 else true))
    (fun i => sk fx h top off P o f2 i (decide (i < off))) off
    (fun i _ => by
      have hp := (peek_lruns W i (fun j => decide (j < off)) (if i = 0 then f1 else true)).dockK
        ![(3 : Fin 9), 7] (by decide) (sk fx h top off P o f2 i (if i = 0 then f1 else true))
        (by intro j; fin_cases j <;> rfl) [1] (by intro j hj; fin_cases j <;> simp at hj ⊢)
      refine hp.congr_out ?_
      funext k; fin_cases k <;> rfl)
    (fun i _ => rfl)
    (fun i hi => by
      have h1 := (moveR_lruns W (1 + i) (sf top)).dockK ![(1 : Fin 9)] (by decide)
        (sk fx h top off P o f2 i (decide (i < off))) (by intro j; fin_cases j; rfl) [0]
        (by intro j hj; fin_cases j; simp at hj)
      have h2 := (moveR_lruns W i (fun j => decide (j < off))).dockK ![(3 : Fin 9)] (by decide)
        (List.foldr (fun k ρ => Function.update ρ ((![(1 : Fin 9)] : Fin 1 → Fin 9) k)
          ((![.cells (sf top) (1 + i + 1)] : Fin 1 → TS) k)) (sk fx h top off P o f2 i (decide (i < off))) [0])
        (by intro j; fin_cases j; rfl) [0] (by intro j hj; fin_cases j; simp at hj)
      refine (h1.seq h2).congr_out ?_
      have e : decide (i < off) = true := decide_eq_true hi
      funext k; fin_cases k <;> simp [sk, e, uw, show 1 + (i + 1) = 1 + i + 1 by omega])
  refine (lr_src hl ?_).congr_out ?_
  · funext k; fin_cases k <;> simp [sk, st0]
  · funext k; fin_cases k <;> simp [sk]

/-- The copy loop's states. -/
def cp (i : ℕ) (b c : Bool) : Fin 9 → TS := ![.cells fx (h + (frame top).length), .cells (sf top) (1 + off + i),
  .cells (sf (List.replicate top.length true)) 1, uw off off, uw P i, sS (o ++ (win top off P).take i),
  sM (o ++ (win top off P).take i), .flag b, .flag c]

/-- The flag of the bit read last. -/
def lastBit (i : ℕ) : Bool := if i = 0 then f2 else sf top (1 + off + (i - 1))

theorem copyBody_run (i : ℕ) (hi : i < P) :
    LRuns W copyBody (1 + 1 + (0 + 1 + 1 + 2 + 1 + (1 + 1 + 1)))
      (cp fx h top off P o i true (lastBit top off f2 i)) (cp fx h top off P o (i + 1) true (lastBit top off f2 (i + 1))) := by
  set bit := sf top (1 + off + i) with hbit
  have e1 := (peek_lruns W (1 + off + i) (sf top) (lastBit top off f2 i)).dockK ![(1 : Fin 9), 8] (by decide)
    (cp fx h top off P o i true (lastBit top off f2 i)) (by intro j; fin_cases j <;> rfl) [1]
    (by intro j hj; fin_cases j <;> simp at hj ⊢)
  have s1 : List.foldr (fun k ρ => Function.update ρ ((![(1 : Fin 9), 8] : Fin 2 → Fin 9) k)
      ((![.cells (sf top) (1 + off + i), .flag (sf top (1 + off + i))] : Fin 2 → TS) k))
      (cp fx h top off P o i true (lastBit top off f2 i)) [1] = cp fx h top off P o i true bit := by
    funext k; fin_cases k <;> rfl
  rw [s1] at e1
  have hw : (o ++ (win top off P).take (i + 1)) = (o ++ (win top off P).take i) ++ [bit] := by
    rw [win_take_succ top off P i hi, List.append_assoc]
  have e2 : LRuns W (Ite (nop 9) (appB true) (appB false) (8 : Fin 9)) (0 + 1 + 1 + 2)
      (cp fx h top off P o i true bit)
      (Function.update (Function.update (cp fx h top off P o i true bit) 5 (sS (o ++ (win top off P).take (i + 1))))
        6 (sM (o ++ (win top off P).take (i + 1)))) := by
    refine Ite.runs (W := W) (np := 1) (nq := 1) (ρ := Function.update (Function.update (cp fx h top off P o i true bit) 5
      (sS (o ++ (win top off P).take (i + 1)))) 6 (sM (o ++ (win top off P).take (i + 1)))) _ _ _ (8 : Fin 9) bit
      (nop_lruns (cp fx h top off P o i true bit)) rfl ?_ ?_
    · intro hb
      have ha := (sapp_lruns W true (o ++ (win top off P).take i)).dockK ![(5 : Fin 9), 6] (by decide)
        (cp fx h top off P o i true bit) (by intro j; fin_cases j <;> rfl) [0, 1]
        (by intro j hj; fin_cases j <;> simp at hj)
      refine ha.congr_out ?_
      rw [hw, ← hb]
      funext k; fin_cases k <;> rfl
    · intro hb
      have ha := (sapp_lruns W false (o ++ (win top off P).take i)).dockK ![(5 : Fin 9), 6] (by decide)
        (cp fx h top off P o i true bit) (by intro j; fin_cases j <;> rfl) [0, 1]
        (by intro j hj; fin_cases j <;> simp at hj)
      refine ha.congr_out ?_
      rw [hw, ← hb]
      funext k; fin_cases k <;> rfl
  have e3 := (moveR_lruns W (1 + off + i) (sf top)).dockK ![(1 : Fin 9)] (by decide)
    (Function.update (Function.update (cp fx h top off P o i true bit) 5 (sS (o ++ (win top off P).take (i + 1))))
      6 (sM (o ++ (win top off P).take (i + 1)))) (by intro j; fin_cases j; rfl) [0]
    (by intro j hj; fin_cases j; simp at hj)
  have e4 := (moveR_lruns W i (fun j => decide (j < P))).dockK ![(4 : Fin 9)] (by decide)
    (List.foldr (fun k ρ => Function.update ρ ((![(1 : Fin 9)] : Fin 1 → Fin 9) k)
      ((![.cells (sf top) (1 + off + i + 1)] : Fin 1 → TS) k))
      (Function.update (Function.update (cp fx h top off P o i true bit) 5 (sS (o ++ (win top off P).take (i + 1))))
        6 (sM (o ++ (win top off P).take (i + 1)))) [0])
    (by intro j; fin_cases j; rfl) [0] (by intro j hj; fin_cases j; simp at hj)
  refine (e1.seq (e2.seq (e3.seq e4))).congr_out ?_
  have hl : lastBit top off f2 (i + 1) = bit := by simp [lastBit, hbit]
  funext k; fin_cases k <;> simp [cp, hl, uw, show 1 + off + (i + 1) = 1 + off + i + 1 by omega]

theorem copy_run : LRuns W copyL ((P + 1) * (1 + (1 + 1 + (0 + 1 + 1 + 2 + 1 + (1 + 1 + 1))) + 2))
    (cp fx h top off P o 0 false f2) (cp fx h top off P o P false (lastBit top off f2 P)) := by
  have hl := Loop.runs (W := W) peekLen copyBody (7 : Fin 9)
    (fun i => cp fx h top off P o i (if i = 0 then false else true) (lastBit top off f2 i))
    (fun i => cp fx h top off P o i (decide (i < P)) (lastBit top off f2 i)) P
    (fun i _ => by
      have hp := (peek_lruns W i (fun j => decide (j < P)) (if i = 0 then false else true)).dockK
        ![(4 : Fin 9), 7] (by decide) (cp fx h top off P o i (if i = 0 then false else true) (lastBit top off f2 i))
        (by intro j; fin_cases j <;> rfl) [1] (by intro j hj; fin_cases j <;> simp at hj ⊢)
      refine hp.congr_out ?_
      funext k; fin_cases k <;> rfl)
    (fun i _ => rfl)
    (fun i hi => by
      have e : decide (i < P) = true := decide_eq_true hi
      rw [e]
      have hb := copyBody_run W fx h top off P o f2 i hi
      refine lr_src hb ?_ |>.congr_out ?_
      · rfl
      · simp)
  refine (lr_src hl ?_).congr_out ?_
  · funext k; fin_cases k <;> simp [cp, lastBit]
  · funext k; fin_cases k <;> simp [cp]

/-- **The window tail**: unframe, skip `off`, copy `P` bits. -/
theorem tail_run (hX : ∀ i, i < (frame top).length → fx (h + i) = (frame top).getD i false) :
    LRuns W tailL (tailCost top.length off P)
      ![.cells fx h, .cells PacketsMeta.blank 0, .cells PacketsMeta.blank 0, uw off 0, uw P 0, sS o, sM o, .flag f1, .flag f2]
      ![.cells fx (h + (frame top).length), .cells (sf top) (1 + off + P),
        .cells (sf (List.replicate top.length true)) 1, uw off off, uw P P, sS (o ++ win top off P),
        sM (o ++ win top off P), .flag false, .flag (lastBit top off f2 P)] := by
  have e1 := unf_run W fx h top off P o f1 f2 hX
  have e2 := skip_run W fx h top off P o f1 f2
  have e3 := copy_run W fx h top off P o f2
  have e23 : sk fx h top off P o f2 off false = cp fx h top off P o 0 false f2 := by
    funext k; fin_cases k <;> simp [sk, cp]
  rw [e23] at e2
  refine (e1.seq (e2.seq e3)).congr_out ?_
  funext k; fin_cases k <;> simp [cp, win_take_all]

end Runs

end
end NearCubicWires.PacketsSymBits.Win
