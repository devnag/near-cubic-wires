import Proof.Packets.PacketsCombineTabGen

/-! # P2 (iii) table writer, part 7: THE TABLE WRITER (the contract for `ThrMeta`'s tape 15)

Consumer: `ThrMeta a K` (`Proof/Packets/PacketsCombineThrLocal.lean`), field `run`, tape 15:
`A 15 = thrTableOf r L target k` = `thrTable D (pop+1) N tupleOf (fun c => modularTupleAccepts prime residue 2
(tupleOf c))` with `H 15 = N * (D*(pop+1) + 1)`, `N = (pop+1)^D`, `D = modulusDigitCount prime`. Paper: A.13.7
(`paper.tex:3113-3142`), internal preprocessing charged in `T_prep` (`paper.tex:1197-1200`); budget class
source-polynomial (`writerCost`: a fixed polynomial of `pop, D, p, res, N`, each `≤ poly(smallSize)`).

`writerM : Machine 12 _` — ONE fixed machine. Local layout: inputs `0` reads as `word pop`, `1` as `word D`,
`2` as `word (D*(pop+1))`, `3` as `word p`, `4` as `word res`, `5` as `word N` (e.g. `UnaryTemplate.tape X` or
`CompareMachine.word X`, head `0`); scratch `6..9, 11` blank; output `10` blank. It runs `genTB` (odometer
tapes), `ucopy` (the register `word (p-1)`), `ucopy` (the loop driver `word N`), then the code loop. Inputs are
only read and their heads return to `0`; the output ends as the table, head at its end.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
noncomputable section

/-! ## Docking helpers -/

theorem install_eq_of {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A B : Fin u → List Bool) (tout : Fin t → List Bool) (h1 : ∀ j, B (slots j) = tout j)
    (h2 : ∀ i, (∀ j, slots j ≠ i) → B i = A i) : install slots A tout = B := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [install_slot slots hi, h1]
  · have hn : ∀ j, slots j ≠ i := fun j hj => h ⟨j, hj⟩
    rw [install_other slots A tout i hn, h2 i hn]

theorem dockH_eq_of {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A B : Fin u → ℕ) (tout : Fin t → ℕ) (h1 : ∀ j, B (slots j) = tout j)
    (h2 : ∀ i, (∀ j, slots j ≠ i) → B i = A i) : dockH slots A tout = B := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [dockH_slot slots hi, h1]
  · have hn : ∀ j, slots j ≠ i := fun j hj => h ⟨j, hj⟩
    rw [dockH_other slots A tout i hn, h2 i hn]

theorem digitsOf_zero (m : ℕ) : ∀ D, digitsOf m D 0 = List.replicate D 0 := by
  intro D
  induction D with
  | zero => rfl
  | succ D ih => rw [digitsOf, Nat.zero_mod, Nat.zero_div, ih, List.replicate_succ]

/-! ## Slots and the machine -/

def slotsG : Fin 5 → Fin 12 := ![0, 1, 6, 7, 8]
def slotsR : Fin 2 → Fin 12 := ![3, 9]
def slotsN : Fin 2 → Fin 12 := ![5, 11]
def slotsL : Fin 9 → Fin 12 := ![6, 7, 8, 2, 9, 3, 4, 10, 11]

theorem slotsG_inj : Function.Injective slotsG := by decide
theorem slotsR_inj : Function.Injective slotsR := by decide
theorem slotsN_inj : Function.Injective slotsN := by decide
theorem slotsL_inj : Function.Injective slotsL := by decide

/-- **The THR selection-table writer** (one fixed machine). -/
def writerM :=
  Composition.machine (Composition.machine (Composition.machine (RecoveryFocus.machine slotsG genTB)
    (RecoveryFocus.machine slotsR (ucopy true false))) (RecoveryFocus.machine slotsN (ucopy false true)))
    (RecoveryFocus.machine slotsL loopM)

/-- The writer's step budget. -/
def writerCost (pop D p res N : ℕ) : ℕ :=
  genCost pop D + 1 + ucopyCost (p - 1) + 1 + ucopyCost N + 1 + loopCost (pop + 1) D p res N

/-- The writer's entry bank. -/
def wIn (Pop Dw KW Pw RSw Nw : List Bool) : Fin 12 → List Bool := ![Pop, Dw, KW, Pw, RSw, Nw, [], [], [], [], [], []]

section Stages
variable (pop D p res N : ℕ) (Pop Dw KW Pw RSw Nw : List Bool)

def wA1 : Fin 12 → List Bool :=
  ![Pop, Dw, KW, Pw, RSw, Nw, [true], Tt (pop + 1) (List.replicate D 0), Bt (pop + 1) D, [], [], []]
def wA2 : Fin 12 → List Bool :=
  ![Pop, Dw, KW, Pw, RSw, Nw, [true], Tt (pop + 1) (List.replicate D 0), Bt (pop + 1) D, CompareMachine.word (p - 1),
    [], []]
def wA3 : Fin 12 → List Bool :=
  ![Pop, Dw, KW, Pw, RSw, Nw, [true], Tt (pop + 1) (List.replicate D 0), Bt (pop + 1) D, CompareMachine.word (p - 1),
    [], CompareMachine.word N]
def wH3 : Fin 12 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def wA4 : Fin 12 → List Bool :=
  ![Pop, Dw, KW, Pw, RSw, Nw, [true], Tt (pop + 1) (digitsOf (pop + 1) D N), Bt (pop + 1) D,
    CompareMachine.word (p - 1), tabPrefix (pop + 1) D p res N, CompareMachine.word N]
def wH4 : Fin 12 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (tabPrefix (pop + 1) D p res N).length, 1]

theorem stageG (hPop : ReadsWord Pop pop) (hDw : ReadsWord Dw D) :
    Step (RecoveryFocus.machine slotsG genTB) (genCost pop D) (fun _ => 0) (wIn Pop Dw KW Pw RSw Nw)
      (fun _ => 0) (wA1 pop D Pop Dw KW Pw RSw Nw) := by
  have e := (genTB_run pop D Pop Dw hPop hDw).dock slotsG slotsG_inj (fun _ => 0) (wIn Pop Dw KW Pw RSw Nw)
    (fun _ => rfl) (by intro j; fin_cases j <;> simp [wIn, slotsG])
  have h : install slotsG (wIn Pop Dw KW Pw RSw Nw)
      ![Pop, Dw, [true], Tt (pop + 1) (List.replicate D 0), Bt (pop + 1) D] = wA1 pop D Pop Dw KW Pw RSw Nw :=
    install_eq_of slotsG slotsG_inj _ _ _ (by intro j; fin_cases j <;> simp [wA1, slotsG])
      (by
        intro i hi
        fin_cases i <;> first | exact ((hi 2) rfl).elim | exact ((hi 3) rfl).elim | exact ((hi 4) rfl).elim |
          simp [wA1, wIn])
  rw [dockH_existing slotsG (fun _ => 0) (fun _ => 0) (fun _ => rfl), h] at e
  exact e

theorem stageR (hp : 1 ≤ p) (hPw : ReadsWord Pw p) :
    Step (RecoveryFocus.machine slotsR (ucopy true false)) (ucopyCost (p - 1)) (fun _ => 0)
      (wA1 pop D Pop Dw KW Pw RSw Nw) (fun _ => 0) (wA2 pop D p Pop Dw KW Pw RSw Nw) := by
  have hPw' : ReadsWord Pw (p - 1 + if true then 1 else 0) := by
    rw [if_pos rfl, Nat.sub_add_cancel hp]; exact hPw
  have e := (ucopy_run true false Pw (p - 1) hPw').dock slotsR slotsR_inj (fun _ => 0) (wA1 pop D Pop Dw KW Pw RSw Nw)
    (fun j => by fin_cases j <;> simp) (by intro j; fin_cases j <;> simp [wA1, slotsR])
  have h : install slotsR (wA1 pop D Pop Dw KW Pw RSw Nw) ![Pw, CompareMachine.word (p - 1)] =
      wA2 pop D p Pop Dw KW Pw RSw Nw :=
    install_eq_of slotsR slotsR_inj _ _ _ (by intro j; fin_cases j <;> simp [wA2, slotsR])
      (by
        intro i hi
        fin_cases i <;> first | exact ((hi 1) rfl).elim | simp [wA1, wA2])
  have hH : dockH slotsR (fun _ => 0) ![0, if false = true then 1 else 0] = fun _ => 0 :=
    dockH_existing slotsR _ _ (fun j => by fin_cases j <;> simp)
  rw [hH, h] at e
  exact e

theorem stageN (hNw : ReadsWord Nw N) :
    Step (RecoveryFocus.machine slotsN (ucopy false true)) (ucopyCost N) (fun _ => 0)
      (wA2 pop D p Pop Dw KW Pw RSw Nw) wH3 (wA3 pop D p N Pop Dw KW Pw RSw Nw) := by
  have hNw' : ReadsWord Nw (N + if false then 1 else 0) := by
    rw [if_neg (by simp), Nat.add_zero]; exact hNw
  have e := (ucopy_run false true Nw N hNw').dock slotsN slotsN_inj (fun _ => 0) (wA2 pop D p Pop Dw KW Pw RSw Nw)
    (fun j => by fin_cases j <;> simp) (by intro j; fin_cases j <;> simp [wA2, slotsN])
  have h : install slotsN (wA2 pop D p Pop Dw KW Pw RSw Nw) ![Nw, CompareMachine.word N] =
      wA3 pop D p N Pop Dw KW Pw RSw Nw :=
    install_eq_of slotsN slotsN_inj _ _ _ (by intro j; fin_cases j <;> simp [wA3, slotsN])
      (by
        intro i hi
        fin_cases i <;> first | exact ((hi 1) rfl).elim | simp [wA2, wA3])
  have hH : dockH slotsN (fun _ => 0) ![0, if true = true then 1 else 0] = wH3 :=
    dockH_eq_of slotsN slotsN_inj _ _ _ (by intro j; fin_cases j <;> simp [wH3, slotsN])
      (by
        intro i hi
        fin_cases i <;> first | exact ((hi 1) rfl).elim | simp [wH3])
  rw [hH, h] at e
  exact e

/-- The loop's row tapes inside the writer. -/
def wW : RowTapes := ⟨[true], Tt (pop + 1) (List.replicate D 0), Bt (pop + 1) D, KW, CompareMachine.word (p - 1), Pw, RSw⟩

theorem stageL (hp : 1 ≤ p) (hKW : ReadsWord KW (D * (pop + 1))) (hPw : ReadsWord Pw p) (hRS : ReadsWord RSw res) :
    Step (RecoveryFocus.machine slotsL loopM) (loopCost (pop + 1) D p res N) wH3 (wA3 pop D p N Pop Dw KW Pw RSw Nw)
      (wH4 pop D p res N) (wA4 pop D p res N Pop Dw KW Pw RSw Nw) := by
  have hl := loop_run (pop + 1) D p res N (by omega) hp (wW pop D p KW Pw RSw) rfl rfl hKW (readsWord_word (p - 1)) hPw hRS
  have hcode0 : codeTapes (wW pop D p KW Pw RSw) (pop + 1) D 0 = wW pop D p KW Pw RSw := by
    unfold codeTapes RowTapes.withT wW
    rw [digitsOf_zero]
  rw [hcode0] at hl
  have e := hl.dock slotsL slotsL_inj wH3 (wA3 pop D p N Pop Dw KW Pw RSw Nw)
    (by intro j; fin_cases j <;> simp [wH3, slotsL, rowH, Fin.addCases])
    (by intro j; fin_cases j <;> simp [wA3, slotsL, rowA, wW, Fin.addCases])
  have h : install slotsL (wA3 pop D p N Pop Dw KW Pw RSw Nw)
      (Fin.addCases (m := 8) (n := 1) (motive := fun _ => List Bool)
        (rowA (codeTapes (wW pop D p KW Pw RSw) (pop + 1) D N) (tabPrefix (pop + 1) D p res N))
        (fun _ : Fin 1 => CompareMachine.word N)) = wA4 pop D p res N Pop Dw KW Pw RSw Nw :=
    install_eq_of slotsL slotsL_inj _ _ _
      (by intro j; fin_cases j <;> simp [wA4, slotsL, rowA, codeTapes, RowTapes.withT, wW, Fin.addCases])
      (by
        intro i hi
        fin_cases i <;> first | exact ((hi 1) rfl).elim | exact ((hi 7) rfl).elim | simp [wA3, wA4])
  have hH : dockH slotsL wH3 (Fin.addCases (m := 8) (n := 1) (motive := fun _ => ℕ)
      (rowH (tabPrefix (pop + 1) D p res N)) (fun _ : Fin 1 => 1)) =
      wH4 pop D p res N :=
    dockH_eq_of slotsL slotsL_inj _ _ _ (by intro j; fin_cases j <;> simp [wH4, slotsL, rowH, Fin.addCases])
      (by
        intro i hi
        fin_cases i <;> first | exact ((hi 7) rfl).elim | simp [wH3, wH4])
  rw [hH, h] at e
  exact e

end Stages

/-- **The table-writer contract.** From inputs reading as `word pop`, `word D`, `word (D*(pop+1))`, `word p`,
`word res`, `word N` (tapes `0..5`, heads `0`) and blank tapes `6..11`, the one fixed machine `writerM` leaves the
inputs and their heads unchanged and writes `tabPrefix (pop+1) D p res N` on tape `10`, head at its end.
(`loop_table`: at `N = (pop+1)^D` this is the consumer's `thrTable … modularTupleAccepts p res 2 …`.) -/
theorem writer_run (pop D p res N : ℕ) (hp : 1 ≤ p) (Pop Dw KW Pw RSw Nw : List Bool)
    (hPop : ReadsWord Pop pop) (hDw : ReadsWord Dw D) (hKW : ReadsWord KW (D * (pop + 1)))
    (hPw : ReadsWord Pw p) (hRS : ReadsWord RSw res) (hNw : ReadsWord Nw N) :
    ∃ (H' : Fin 12 → ℕ) (A' : Fin 12 → List Bool),
      Step writerM (writerCost pop D p res N) (fun _ => 0) (wIn Pop Dw KW Pw RSw Nw) H' A' ∧
      (∀ i : Fin 12, i.val < 6 → A' i = wIn Pop Dw KW Pw RSw Nw i ∧ H' i = 0) ∧
      A' 10 = tabPrefix (pop + 1) D p res N ∧ H' 10 = (tabPrefix (pop + 1) D p res N).length := by
  refine ⟨wH4 pop D p res N, wA4 pop D p res N Pop Dw KW Pw RSw Nw,
    (((stageG pop D Pop Dw KW Pw RSw Nw hPop hDw).seq (stageR pop D p Pop Dw KW Pw RSw Nw hp hPw)).seq
      (stageN pop D p N Pop Dw KW Pw RSw Nw hNw)).seq (stageL pop D p res N Pop Dw KW Pw RSw Nw hp hKW hPw hRS),
    ?_, rfl, rfl⟩
  intro i hi
  fin_cases i <;> simp_all [wA4, wH4, wIn]

end

end NearCubicWires.PacketsCombine.Tab

