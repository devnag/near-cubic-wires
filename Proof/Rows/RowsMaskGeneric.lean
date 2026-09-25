import Proof.Rows.RowsCellGeneric
import Proof.Rows.RowsThrMask

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.MaskGeneric
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.BlockPlatform RowsConstruction.ThrCell RowsConstruction.ThrMask
open RowsConstruction.CellGeneric
noncomputable section

/-- **The fixed per-cell machine** for verdict machine `V`. -/
def gbody {sV : Nat} (V : Machine 254 sV) (H0 : Fin 254 → ℕ) :=
  Composition.machine scatterStage (Composition.machine (TapeEmbedding.machine 7 (cellMachine V H0))
    (Composition.machine eraseStage incStage))

/-- Everything one row's mask needs, stated once. -/
structure Premises {q sV : Nat} (V : Machine 254 sV) (H0 : Fin 254 → ℕ)
    (inp : BitInput q → Fin 254 → List Bool) (vb : BitInput q → Bool) (nx : BitInput q → Nat)
    (live : Finset (Fin q)) (s R Cl Dl Nt : Nat) (M : Fin 254 → List Bool) : Prop where
  hle : ∀ i, H0 i ≤ 1
  run : ∀ x, ∃ J B, Step V (nx x) H0 (inp x) J B ∧ J 253 = 0 ∧ readTapeBit (B 253) 0 = vb x
  m109 : M 109 = List.replicate R false
  mlen : ∀ i, (M i).length ≤ R
  mne : ∀ (x : BitInput q) (i : Fin 254), i ≠ 109 → ZeroPadding.pad R (M i) = ZeroPadding.pad R (inp x i)
  in109 : ∀ x, inp x 109 = List.ofFn x
  qR : q ≤ R
  sR : (s+1)/2+s/2 ≤ R
  cl : 2*((s+1)/2)+1 ≤ Cl
  cr : 2*(s/2)+1 ≤ Cl
  dl : 4*((s+1)/2+s/2)+7 ≤ Dl
  dq : 4*q+3 ≤ Dl
  di : 2*((s+1)/2)+1 ≤ Dl
  n : ∀ x, nx x ≤ Nt
  nt : Nt+2 ≤ R

variable {q sV : Nat} {V : Machine 254 sV} {H0 : Fin 254 → ℕ} {inp : BitInput q → Fin 254 → List Bool}
  {vb : BitInput q → Bool} {nx : BitInput q → Nat} {live : Finset (Fin q)} {s R Cl Dl Nt : Nat}
  {M : Fin 254 → List Bool}

/-- **One cell** `(rowN, colN)`: appends `vb` at the cell's `printerPoint`, advances the column. -/
theorem gbody_step (h : Premises V H0 inp vb nx live s R Cl Dl Nt M) (ha : (s+1)/2+s/2=liveᶜ.card)
    (rowN colN : Nat) (out : List Bool) :
    Step (gbody V H0) (bodyCost s q R Nt)
      (heads out.length) (tapes live s R Cl Dl rowN colN M out)
      (heads (out++[vb (point live s ha rowN colN)]).length)
      (tapes live s R Cl Dl rowN (colN+1) M (out++[vb (point live s ha rowN colN)])) := by
  let x := point live s ha rowN colN
  let pt := C10ExternalRowLoop.printerPoint live s ha rowN colN
  let M' := Function.update M 109 (ZeroPadding.pad R (List.ofFn x))
  have hxlen : (List.ofFn x).length ≤ R := by simp [h.qR]
  have hptlen : (List.ofFn pt).length ≤ R := by
    rw [List.length_ofFn, ← ha]; exact h.sR
  have s1 := scatter_step live s ha R Cl Dl rowN colN M h.m109
    (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out)
    (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) out.length) h.qR h.sR h.cl h.cr h.dl h.dq
  have hM'l : ∀ i, (M' i).length ≤ R := by
    intro i
    by_cases hi : i = 109
    · subst hi
      simp only [M', Function.update_self, ZeroPadding.pad_length]
      exact max_le (le_refl _) hxlen
    · simp only [M', Function.update_of_ne hi]
      exact h.mlen i
  have hM' : ∀ i, ZeroPadding.pad R (M' i) = ZeroPadding.pad R (inp x i) := by
    intro i
    by_cases hi : i = 109
    · subst hi
      simp only [M', Function.update_self]
      rw [MatrixBucketRootPower.pad_pad R R _ le_rfl, h.in109 x]
    · simp only [M', Function.update_of_ne hi]
      exact h.mne x i hi
  obtain ⟨J, B, hrun, hJ, hbit⟩ := h.run x
  have s2core := (cell_step V H0 h.hle R out M' (inp x) (nx x) J B (vb x) hrun hJ hbit hM'l hM'
    (by have := h.n x; have := h.nt; omega)).enlarge (m := 2*R+4+1+(1+1+(Nt+4*R+12)))
    (by have := h.n x; omega)
  have s2 := s2core.embed auxHeads (aux live s Cl Dl rowN colN (ZeroPadding.pad R (List.ofFn pt)))
  have s3 := erase_step R
    (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R (out++[vb x]))
    (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) (out++[vb x]).length) M'
    (aux live s Cl Dl rowN colN (ZeroPadding.pad R (List.ofFn pt))) auxHeads rfl rfl rfl rfl rfl
    (hM'l 109) (by
      show (ZeroPadding.pad R (List.ofFn pt)).length ≤ R
      rw [ZeroPadding.pad_length]; exact max_le (le_refl _) hptlen)
  have hMback : Function.update M' 109 (List.replicate R false) = M := by
    simp only [M', Function.update_idem]
    rw [← h.m109, Function.update_eq_self]
  rw [hMback, aux_erase] at s3
  have s4 := inc_stage_step
    (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R (out++[vb x]))
    (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) (out++[vb x]).length) M live s R Cl Dl rowN colN
    (by have := h.di; omega)
  exact s1.seq (s2.seq (s3.seq s4))

/-- **Inner loop**: all `2^(s/2)` columns of printed row `rowN`. -/
def ginner (h : Premises V H0 inp vb nx live s R Cl Dl Nt M) (ha : (s+1)/2+s/2=liveᶜ.card) (rowN : Nat) :=
  Cells.mk (t:=MT) (gbody V H0) (bodyCost s q R Nt) (2^(s/2))
    (fun j out => ⟨(gbody V H0).start, heads out.length, tapes live s R Cl Dl rowN j M out⟩)
    (fun j => [vb (point live s ha rowN j)])
    (fun _ _ _ => rfl)
    (fun j _ out => gbody_step h ha rowN j out)

def gouterBody {sV' : Nat} (V' : Machine 254 sV') (H0' : Fin 254 → ℕ) :=
  Composition.machine (CloseoutRowsDegreeLoop.machine (gbody V' H0')) (TapeEmbedding.machine 1 rowIncStage)

theorem gouter_step (h : Premises V H0 inp vb nx live s R Cl Dl Nt M) (ha : (s+1)/2+s/2=liveᶜ.card)
    (rowN : Nat) (out : List Bool) :
    Step (gouterBody V H0) (rowCost s q R Nt)
      (Fin.addCases (heads out.length) (fun _ : Fin 1 => 1))
      (Fin.addCases (tapes live s R Cl Dl rowN 0 M out) (fun _ : Fin 1 => CompareMachine.word (2^(s/2))))
      (Fin.addCases (heads (out ++ (List.range (2^(s/2))).flatMap
        (fun j => [vb (point live s ha rowN j)])).length) (fun _ : Fin 1 => 1))
      (Fin.addCases (tapes live s R Cl Dl (rowN+1) 0 M (out ++ (List.range (2^(s/2))).flatMap
        (fun j => [vb (point live s ha rowN j)])))
        (fun _ : Fin 1 => CompareMachine.word (2^(s/2)))) := by
  have s1 := cells_step (ginner h ha rowN) out
  change Step _ _ _ _ _ (Fin.addCases (tapes live s R Cl Dl rowN (2^(s/2)) M _) _) at s1
  rw [tapes_wrap] at s1
  have s2 := (rowInc_step (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R
      (out ++ (List.range (2^(s/2))).flatMap (fun j => [vb (point live s ha rowN j)])))
    (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0)
      (out ++ (List.range (2^(s/2))).flatMap (fun j => [vb (point live s ha rowN j)])).length)
    M live s R Cl Dl rowN h.di).embed (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word (2^(s/2)))
  exact s1.seq s2

def gouter (h : Premises V H0 inp vb nx live s R Cl Dl Nt M) (ha : (s+1)/2+s/2=liveᶜ.card) :=
  Cells.mk (t:=MT+1) (gouterBody V H0) (rowCost s q R Nt) (2^((s+1)/2))
    (fun i out => ⟨(gouterBody V H0).start, Fin.addCases (heads out.length) (fun _ : Fin 1 => 1),
      Fin.addCases (tapes live s R Cl Dl i 0 M out) (fun _ : Fin 1 => CompareMachine.word (2^(s/2)))⟩)
    (fun i => (List.range (2^(s/2))).flatMap (fun j => [vb (point live s ha i j)]))
    (fun _ _ _ => rfl)
    (fun i _ out => gouter_step h ha i out)

theorem gemit_gridWord (ha : (s+1)/2+s/2=liveᶜ.card) :
    (List.range (2^((s+1)/2))).flatMap
        (fun i => (List.range (2^(s/2))).flatMap (fun j => [vb (point live s ha i j)])) =
      PCJ45bee56da9f34d5a_SelectionWord.gridWord live s ha
        (fun z => vb (C10SupplierRowInput.joinInput live (fun _ => false) z)) := by
  have hs : 2^s = 2^((s+1)/2)*2^(s/2) := by rw [← pow_add]; congr 1; omega
  unfold PCJ45bee56da9f34d5a_SelectionWord.gridWord
  rw [hs, range_mul_map]
  apply List.flatMap_congr
  intro i _
  rw [flatMap_singleton_map]
  apply List.map_congr_left
  intro j hj
  have hj' : j < 2^(s/2) := List.mem_range.mp hj
  have hpos : 0 < 2^(s/2) := Nat.pow_pos (by decide)
  have hdiv : (i*2^(s/2)+j)/2^(s/2) = i := by
    rw [Nat.mul_comm i, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj', Nat.add_zero]
  have hmod : (i*2^(s/2)+j)%2^(s/2) = j := by
    rw [Nat.mul_comm i, Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
  rw [hdiv, hmod]
  rfl

/-- **The row's whole selection mask, any verdict machine.** One fixed machine
(`CloseoutRowsDegreeLoop.machine (gouterBody V H0)`), from resident masters `M` (port 109 blank) and both
cursors at 0, appends `gridWord live s harity (fun z => vb (joinInput live (fun _ => false) z))` to the
verdict tape and returns every other port, both cursors and both loop counters. -/
theorem gmask (h : Premises V H0 inp vb nx live s R Cl Dl Nt M) (ha : (s+1)/2+s/2=liveᶜ.card)
    (out : List Bool) :
    Step (CloseoutRowsDegreeLoop.machine (gouterBody V H0)) (2^((s+1)/2)*(rowCost s q R Nt+3)+3)
      (Fin.addCases (Fin.addCases (heads out.length) (fun _ : Fin 1 => 1)) (fun _ : Fin 1 => 1))
      (Fin.addCases (Fin.addCases (tapes live s R Cl Dl 0 0 M out)
        (fun _ : Fin 1 => CompareMachine.word (2^(s/2))))
        (fun _ : Fin 1 => CompareMachine.word (2^((s+1)/2))))
      (Fin.addCases (Fin.addCases (heads (out ++ PCJ45bee56da9f34d5a_SelectionWord.gridWord live s ha
        (fun z => vb (C10SupplierRowInput.joinInput live (fun _ => false) z))).length)
        (fun _ : Fin 1 => 1)) (fun _ : Fin 1 => 1))
      (Fin.addCases (Fin.addCases (tapes live s R Cl Dl 0 0 M (out ++
        PCJ45bee56da9f34d5a_SelectionWord.gridWord live s ha
          (fun z => vb (C10SupplierRowInput.joinInput live (fun _ => false) z))))
        (fun _ : Fin 1 => CompareMachine.word (2^(s/2))))
        (fun _ : Fin 1 => CompareMachine.word (2^((s+1)/2)))) := by
  have loop := cells_step (gouter h ha) out
  have hT : ∀ X, ((gouter h ha).source (gouter h ha).bound X).tapes =
      Fin.addCases (tapes live s R Cl Dl 0 0 M X) (fun _ : Fin 1 => CompareMachine.word (2^(s/2))) := by
    intro X
    rw [← tapes_wrap_row]
    rfl
  have hE : (List.range (gouter h ha).bound).flatMap (gouter h ha).emit =
      PCJ45bee56da9f34d5a_SelectionWord.gridWord live s ha
        (fun z => vb (C10SupplierRowInput.joinInput live (fun _ => false) z)) :=
    gemit_gridWord ha
  rw [hT, hE] at loop
  exact loop

end
end RowsConstruction.MaskGeneric
