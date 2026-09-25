import Proof.Packets.PacketsCombineTabHorner

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-! ## The per-code body -/

/-- The odometer on tapes `0..2` of the row layout. -/
def odo8 : Machine 8 8 := TapeEmbedding.machine 5 odo

/-- One code: its row, then the increment of its digit tuple. -/
def bodyM : Machine 8 (22 + 8) := Composition.machine rowM odo8

/-- The row tapes with a new tuple tape. -/
def RowTapes.withT (W : RowTapes) (T : List Bool) : RowTapes := ⟨W.L, T, W.B, W.KW, W.R, W.R2, W.RS⟩

theorem odo8_run (m D : ℕ) (hm : 1 ≤ m) (ds : List ℕ) (hds : ∀ y ∈ ds, y < m) (hD : ds.length = D)
    (W : RowTapes) (hL : W.L = [true]) (hT : W.T = Tt m ds) (hB : W.B = Bt m D) (o : List Bool) :
    Step odo8 (odoBudget m D) (rowH o) (rowA W o) (rowH o) (rowA (W.withT (Tt m (incr m ds))) o) := by
  have h := (odo_run m D hm ds hds hD).embed (![0, 0, 0, 0, o.length] : Fin 5 → ℕ)
    (![W.KW, W.R, W.R2, W.RS, o] : Fin 5 → List Bool)
  have hH : (Fin.addCases (fun _ : Fin 3 => 0) (![0, 0, 0, 0, o.length] : Fin 5 → ℕ) : Fin (3 + 5) → ℕ) = rowH o := by
    funext i; fin_cases i <;> rfl
  have hA : (Fin.addCases (![[true], Tt m ds, Bt m D] : Fin 3 → List Bool)
      (![W.KW, W.R, W.R2, W.RS, o] : Fin 5 → List Bool) : Fin (3 + 5) → List Bool) = rowA W o := by
    funext i; fin_cases i
    · exact hL.symm
    · exact hT.symm
    · exact hB.symm
    all_goals rfl
  have hA' : (Fin.addCases (![[true], Tt m (incr m ds), Bt m D] : Fin 3 → List Bool)
      (![W.KW, W.R, W.R2, W.RS, o] : Fin 5 → List Bool) : Fin (3 + 5) → List Bool) =
      rowA (W.withT (Tt m (incr m ds))) o := by
    funext i; fin_cases i
    · exact hL.symm
    · rfl
    · exact hB.symm
    all_goals rfl
  rw [hH, hA, hA'] at h
  exact h

/-- The acceptance-row output of one code. -/
theorem rowOf_eq (m D p res c : ℕ) :
    rowOf m D p res c = blocksOf m (digitsOf m D c) ++ [decide ((res + radixList (digitsOf m D c) 0) % p = 0)] := rfl

/-- The row tapes of code `i`. -/
def codeTapes (W : RowTapes) (m D i : ℕ) : RowTapes := W.withT (Tt m (digitsOf m D i))

/-- **One code**: bank of code `i` to bank of code `i+1`. -/
theorem body_run (m D p res : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (W : RowTapes) (hL : W.L = [true])
    (hB : W.B = Bt m D) (hK : ReadsWord W.KW (D * m)) (hR : ReadsWord W.R (p - 1)) (hR2 : ReadsWord W.R2 p)
    (hRS : ReadsWord W.RS res) (i : ℕ) :
    Step bodyM (rowCost m D p res + 1 + odoBudget m D)
      (rowH (tabPrefix m D p res i)) (rowA (codeTapes W m D i) (tabPrefix m D p res i))
      (rowH (tabPrefix m D p res (i + 1))) (rowA (codeTapes W m D (i + 1)) (tabPrefix m D p res (i + 1))) := by
  have hds := digitsOf_lt m hm D i
  have hD := digitsOf_length m D i
  have r := row_run m D p res hm hp (codeTapes W m D i) hL (digitsOf m D i) hds hD rfl hB hK hR hR2 hRS
    (tabPrefix m D p res i)
  have o := odo8_run m D hm (digitsOf m D i) hds hD (codeTapes W m D i) hL rfl hB
    (tabPrefix m D p res i ++ (blocksOf m (digitsOf m D i) ++ [decide ((res + radixList (digitsOf m D i) 0) % p = 0)]))
  rw [incr_digitsOf m hm D i] at o
  have hs := r.seq o
  rw [← rowOf_eq] at hs
  exact hs

/-! ## The code loop -/

/-- The whole table loop: `bodyM` repeated `N` times, driven by `CompareMachine.word N` (tape 8). -/
def loopM := RepeatMachine.machine bodyM (fun _ _ => true)

/-- The loop's step budget. -/
def loopCost (m D p res N : ℕ) : ℕ := N * (rowCost m D p res + 1 + odoBudget m D + 3) + 3

theorem loop_run (m D p res N : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (W : RowTapes) (hL : W.L = [true])
    (hB : W.B = Bt m D) (hK : ReadsWord W.KW (D * m)) (hR : ReadsWord W.R (p - 1)) (hR2 : ReadsWord W.R2 p)
    (hRS : ReadsWord W.RS res) :
    Step loopM (loopCost m D p res N)
      (Fin.addCases (rowH []) (fun _ : Fin 1 => 1))
      (Fin.addCases (rowA (codeTapes W m D 0) []) (fun _ : Fin 1 => CompareMachine.word N))
      (Fin.addCases (rowH (tabPrefix m D p res N)) (fun _ : Fin 1 => 1))
      (Fin.addCases (rowA (codeTapes W m D N) (tabPrefix m D p res N)) (fun _ : Fin 1 => CompareMachine.word N)) :=
  PhysicalRepeatStep.run bodyM N (rowCost m D p res + 1 + odoBudget m D)
    (fun i => rowH (tabPrefix m D p res i)) (fun i => rowA (codeTapes W m D i) (tabPrefix m D p res i))
    (fun i _ => body_run m D p res hm hp W hL hB hK hR hR2 hRS i)

end

end NearCubicWires.PacketsCombine.Tab

