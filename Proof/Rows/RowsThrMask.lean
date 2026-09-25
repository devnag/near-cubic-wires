import Proof.Rows.RowsThrCell
import Proof.Rows.SelectionWord
import Proof.MachineModel.BlockLoop

/-! # Rows C3(d), part 2: the whole THR selection mask of one external row

**Consumer.** Warm field 2 of the row's `datumFields` is `gridWord live s harity row.select`
(`SelectionWord.mask_cells_printerPoint`, `…_SelectionWord.lean:108`; `warmFields_selection` `:141`).
For a THR row `row.select z = decide (modularOffset occ live (joinInput live (fun _ => false) z)
(equation a r sel) p = o)` (`Packets.thrFamily`, `fixed-live-packet-parent-20260921/PCJ9eff70d512234a4c_Packets.lean:74`).
`thr_mask` below appends EXACTLY that word to the verdict tape, from resident masters, in
`printerPoint` order, by one fixed machine (two nested `Cells` loops over `RowsThrCell.body`).

**Paper.** `paper.tex:1190-1212`: "One external row … is charged one complete `2^{q-K}`-column score
table." Budget class: TABLE — `2^((s+1)/2)` outer iterations of `2^(s/2)` cells, each cell a cost
polynomial in the request (`R`, `Bt`, `q`, `s`); nothing of `copyCap`, `smallSize` or `2^K` is multiplied
into it. Both cursors return to 0 and both loop counters are restored, so the loop is re-entrant.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrMask
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution SignedSortKey
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.BlockPlatform NearCubicWires.SupplierEstimator RowsConstruction.ThrCell
noncomputable section

/-! ## 0. Flat enumeration = rows of columns -/

theorem range_mul_map {α : Type} (a b : Nat) (f : Nat → α) :
    (List.range (a*b)).map f =
      (List.range a).flatMap (fun i => (List.range b).map (fun j => f (i*b+j))) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.map_map]
    rfl

theorem flatMap_singleton_map {α : Type} (l : List Nat) (g : Nat → α) :
    l.flatMap (fun j => [g j]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ## 1. A loop's receipt as a `Step` -/

theorem cells_step {t s : Nat} (c : Cells t s) (out : List Bool) :
    Step (CloseoutRowsDegreeLoop.machine c.body) (c.bound*(c.cost+3)+3)
      (Fin.addCases (c.source 0 out).heads (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source 0 out).tapes (fun _ : Fin 1 => CompareMachine.word c.bound))
      (Fin.addCases (c.source c.bound (out ++ (List.range c.bound).flatMap c.emit)).heads
        (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source c.bound (out ++ (List.range c.bound).flatMap c.emit)).tapes
        (fun _ : Fin 1 => CompareMachine.word c.bound)) := by
  obtain ⟨r, hr, hf, _⟩ := c.run out
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

/-! ## 2. The row-cursor increment (on the cell layout) -/

def rowSlots : Fin 2 → Fin MT := ![auxP 0, auxP 4]
theorem rowSlots_val (j : Fin 2) : (rowSlots j).val = ![511, 515] j := by
  fin_cases j <;> rfl
theorem rowSlots_injective : Function.Injective rowSlots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [rowSlots_val, rowSlots_val] at hv
  fin_cases a <;> fin_cases b <;> simp at hv ⊢

def rowIncStage := RecoveryFocus.machine rowSlots PCJ45bee56da9f34d5a_CountFlags.inc

theorem rowInc_step (X : Fin 257 → List Bool) (HX : Fin 257 → ℕ) (M : Fin 254 → List Bool)
    {q : Nat} (live : Finset (Fin q)) (s R C D rowN : Nat) (hDi : 2*((s+1)/2)+1 ≤ D) :
    Step rowIncStage (4*((s+1)/2)+4)
      (layout HX (fun _ => 0) auxHeads) (layout X M (aux live s C D rowN 0 (List.replicate R false)))
      (layout HX (fun _ => 0) auxHeads)
      (layout X M (aux live s C D (rowN+1) 0 (List.replicate R false))) := by
  have base := inc_step ((s+1)/2) rowN D hDi
  have focused := base.focus rowSlots rowSlots_injective (layout HX (fun _ => 0) auxHeads)
    (layout X M (aux live s C D rowN 0 (List.replicate R false)))
  have hH : dockH rowSlots (layout HX (fun _ => 0) auxHeads) (fun _ => 0) =
      layout HX (fun _ => 0) auxHeads := by
    apply dockH_existing
    intro j
    fin_cases j <;> rfl
  have hA : install rowSlots (layout X M (aux live s C D rowN 0 (List.replicate R false)))
      (![frame (binary ((s+1)/2) rowN), List.replicate D false] : Fin 2 → List Bool) =
      layout X M (aux live s C D rowN 0 (List.replicate R false)) := by
    apply install_existing
    intro j
    fin_cases j
    · change layout X M _ (auxP 0) = _; simp [aux]
    · change layout X M _ (auxP 4) = _; simp [aux]
  have hO : install rowSlots (layout X M (aux live s C D rowN 0 (List.replicate R false)))
      (![frame (binary ((s+1)/2) (rowN+1)), List.replicate D false] : Fin 2 → List Bool) =
      layout X M (aux live s C D (rowN+1) 0 (List.replicate R false)) := by
    funext x
    refine cover (motive := fun x => install rowSlots
      (layout X M (aux live s C D rowN 0 (List.replicate R false)))
      (![frame (binary ((s+1)/2) (rowN+1)), List.replicate D false] : Fin 2 → List Bool) x =
      layout X M (aux live s C D (rowN+1) 0 (List.replicate R false)) x)
      (fun i => ?_) (fun k => ?_) (fun j => ?_) x
    · rw [install_other _ _ _ _ (fun j h => by
        have hv := congrArg Fin.val h
        rw [rowSlots_val, cellP_val] at hv
        have := i.isLt
        fin_cases j <;> simp at hv <;> omega)]
      simp
    · rw [install_other _ _ _ _ (fun j h => by
        have hv := congrArg Fin.val h
        rw [rowSlots_val, masterP_val] at hv
        have := k.isLt
        fin_cases j <;> simp at hv <;> omega)]
      simp
    · rw [layout_aux]
      by_cases h0 : j = 0
      · subst h0
        change install rowSlots _ _ (rowSlots 0) = _
        rw [install_slot _ rowSlots_injective]
        rfl
      · by_cases h4 : j = 4
        · subst h4
          change install rowSlots _ _ (rowSlots 1) = _
          rw [install_slot _ rowSlots_injective]
          rfl
        · rw [install_other _ _ _ _ (fun j' h => by
            have hv := congrArg Fin.val h
            rw [rowSlots_val, auxP_val] at hv
            have e0 : j.val ≠ 0 := fun h' => h0 (Fin.ext h')
            have e4 : j.val ≠ 4 := fun h' => h4 (Fin.ext h')
            have := j.isLt
            fin_cases j' <;> simp at hv <;> omega), layout_aux]
          fin_cases j <;> simp_all [aux]
  rw [hH, hA, hO] at focused
  exact focused

/-- The column cursor wraps: after `2^(s/2)` increments the state is the column-0 state. -/
theorem tapes_wrap {q : Nat} (live : Finset (Fin q)) (s R C D rowN : Nat) (M : Fin 254 → List Bool)
    (out : List Bool) :
    tapes live s R C D rowN (2^(s/2)) M out = tapes live s R C D rowN 0 M out := by
  unfold tapes aux
  rw [binary_mod (s/2) (2^(s/2)), Nat.mod_self]

theorem tapes_wrap_row {q : Nat} (live : Finset (Fin q)) (s R C D : Nat) (M : Fin 254 → List Bool)
    (out : List Bool) :
    tapes live s R C D (2^((s+1)/2)) 0 M out = tapes live s R C D 0 0 M out := by
  unfold tapes aux
  rw [binary_mod ((s+1)/2) (2^((s+1)/2)), Nat.mod_self]

/-! ## 3. The two loops -/

variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q))
  {cutoff : Nat} (prime : PrimeIndex cutoff) (o : Fin prime.val) (T L target w F U v C P : Nat)
  (s : Nat) (ha : (s+1)/2+s/2=Iᶜ.card) (R Cl Dl Bt : Nat) (M : Fin 254 → List Bool)

variable {a r four sel I prime o T L target w F U v C P s R Cl Dl Bt M}

def rowCost (s q R Bt : Nat) : Nat := 2^(s/2)*(bodyCost s q R Bt+3)+3+1+(4*((s+1)/2)+4)

end
end RowsConstruction.ThrMask
