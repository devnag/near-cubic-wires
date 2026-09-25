import Proof.Rows.RowsMaskStage

/-! # Rows `complete` on the work block: the row's mask (both modes) and the verdict erase

**Consumer.** `complete`'s work-block duties between the row-level stages (rows-rowlevel `rowLevel_step`, C6
`frame_step`): C3 — leave the family row's selection mask on the verdict tape (`thr_mask_work`/`sym_mask_work`, from
`base j`, all heads `0`); then, after C6 has placed it, restore the verdict tape to `0^(2^s)` (`erase_work`) so that C5
(`RowsThrC5.thr_c5` / RC5's SYM C5) reaches `base (j+1)` exactly.
**Machines.** `maskW M := RecoveryFocus.machine lslots (maskStage M)` (the loop block + the two C6 words docked on the
work block), `eraseW := RecoveryFocus.machine eslots (RecoveryScratchErase.resetMachine 1)` (driver = C6 `1^(2^s)`, log
= C6 `0^(2·2^s+1)`).
**Paper.** `paper.tex:1190-1212`. **Budget.** Once per row: the mask loop (table class, one `2^s` factor) + `O(2^s)`.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CompleteWork
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open RowsConstruction.BaseLayout RowsConstruction.ThrCell RowsConstruction.MaskStage
noncomputable section

/-! ## 1. Ports -/

section Ports
variable (NI : Nat)

/-- The loop block and the two C6 words, on the work block. -/
def lslots : Fin (MaskStage.LT+2) → Fin (2+rowsWork NI) := Fin.addCases (loopPort NI) (c6Port NI)

theorem loopPort_val (i : Fin LT) : (loopPort NI i).val = 2+NI+72+i.val := by
  simp [loopPort, fixPort]
  omega

theorem c6Port_val (i : Fin 2) : (c6Port NI i).val = 2+NI+72+520+i.val := by
  simp [c6Port, fixPort, MT]
  omega

theorem lslots_val (i : Fin (MaskStage.LT+2)) : (lslots NI i).val = 2+NI+72+i.val := by
  unfold lslots
  refine Fin.addCases (fun y => ?_) (fun z => ?_) i
  · rw [Fin.addCases_left, loopPort_val]; simp
  · rw [Fin.addCases_right, c6Port_val]; simp [MaskStage.LT, MT]; omega

theorem lslots_injective : Function.Injective (lslots NI) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [lslots_val, lslots_val] at hv
  exact Fin.ext (by omega)

/-- Every local port is a loop-block port or a C6 word. -/
theorem split2 (j : Fin (MaskStage.LT+2)) :
    (∃ y : Fin MaskStage.LT, j = y.castAdd 2) ∨ (∃ z : Fin 2, j = Fin.natAdd MaskStage.LT z) := by
  by_cases h : j.val < MaskStage.LT
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨j.val - MaskStage.LT, by have := j.isLt; omega⟩, Fin.ext (by simp; omega)⟩

/-- The verdict tape, C6 driver and C6 log on the work block. -/
def eslots : Fin 3 → Fin (2+rowsWork NI) := ![loopPort NI vL, c6Port NI 0, c6Port NI 1]

theorem eslots_injective : Function.Injective (eslots NI) := by
  intro x y h
  have hv := congrArg Fin.val h
  fin_cases x <;> fin_cases y <;> simp [eslots, loopPort_val, c6Port_val, vL] at hv ⊢

/-- **The docked mask stage** (one fixed machine per loop machine `M`). -/
def maskW {sM : Nat} (M : Machine MaskStage.LT sM) := RecoveryFocus.machine (lslots NI) (maskStage M)

/-- **The verdict erase** (one fixed machine). -/
def eraseW := RecoveryFocus.machine (eslots NI) (RecoveryScratchErase.resetMachine 1)

end Ports

/-! ## 2. The two stages on any work bank -/

theorem mask_work (NI : Nat) {q : Nat} (live : Finset (Fin q)) (s R C D : Nat) (Ms : Fin 254 → List Bool)
    (w : List Bool) (hw : w.length = 2^s) {sM : Nat} (M : Machine MaskStage.LT sM) (n : Nat)
    (hM : Step M n (loopH 0) (loopT live s R C D Ms []) (loopH w.length) (loopT live s R C D Ms w))
    (A : Fin (2+rowsWork NI) → List Bool)
    (hA : ∀ i, A (lslots NI i) = localT live s R C D Ms (List.replicate (2^s) false) i) :
    Step (maskW NI M) (1+1+(n+1+(1+1+(2*2^s+2)))) (fun _ => 0) A (fun _ => 0)
      (Function.update A (loopPort NI vL) w) := by
  have d := RowsConstruction.ThrKey.wdock NI (mask_step live s R C D Ms w hw M n hM) (lslots NI)
    (lslots_injective NI) A hA
  rw [SymVerdict.install_update _ (lslots_injective NI) A _ (vL.castAdd 2) (fun j hj => by
    rw [hA j]
    unfold localT
    rcases split2 j with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Fin.addCases_left, Fin.addCases_left]
      exact loopT_off live s R C D Ms w _ y (fun e => hj (by rw [e]))
    · rw [Fin.addCases_right, Fin.addCases_right])] at d
  exact d

theorem erase_work (NI : Nat) (s : Nat) (w : List Bool) (hw : w.length ≤ 2^s) (A : Fin (2+rowsWork NI) → List Bool)
    (hv : A (loopPort NI vL) = w) (hd : A (c6Port NI 0) = List.replicate (2^s) true)
    (hg : A (c6Port NI 1) = List.replicate (2*2^s+1) false) :
    Step (eraseW NI) (2*2^s+4) (fun _ => 0) A (fun _ => 0)
      (Function.update A (loopPort NI vL) (List.replicate (2^s) false)) := by
  have h := Step.of_ready (RecoveryScratchErase.erase_ready (t := 1) (2^s) (2*2^s+1) (fun _ => w) (fun _ => hw))
  have e1 : (Fin.addCases (motive := fun _ : Fin (1+1+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => w)
        (fun _ : Fin 1 => List.replicate (2^s) true)) (fun _ : Fin 1 => List.replicate (2*2^s+1) false)) =
      ![w, List.replicate (2^s) true, List.replicate (2*2^s+1) false] := by
    funext i; fin_cases i <;> rfl
  have hm : max (2*2^s+1) (2^s+1) = 2*2^s+1 := by omega
  rw [hm] at h
  have e2 : (Fin.addCases (motive := fun _ : Fin (1+1+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => List.replicate (2^s) false)
        (fun _ : Fin 1 => List.replicate (2^s) true))
        (fun _ : Fin 1 => List.replicate (2*2^s+1) false)) =
      ![List.replicate (2^s) false, List.replicate (2^s) true, List.replicate (2*2^s+1) false] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2] at h
  have d := RowsConstruction.ThrKey.wdock NI h (eslots NI) (eslots_injective NI) A (fun j => by
    fin_cases j
    · exact hv
    · exact hd
    · exact hg)
  rw [SymVerdict.install_update _ (eslots_injective NI) A _ 0 (fun j hj => by
    fin_cases j
    · exact absurd rfl hj
    · exact hd.symm
    · exact hg.symm)] at d
  exact d

/-! ## 3. THR and SYM rows -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- The THR loop machine. -/
abbrev thrLoop := CloseoutRowsDegreeLoop.machine (MaskGeneric.gouterBody PCJ45bee56da9f34d5a_ThresholdTraversal.machine
  PCJ45bee56da9f34d5a_ThresholdTraversal.initialHeads)

/-- The THR mask cost. -/
abbrev thrMaskCost : Nat :=
  1+1+((2^(((thrLive r L)ᶜ.card+1)/2)*(ThrMask.rowCost (thrLive r L)ᶜ.card r.q
    (KeyTop.RT a r four L target) (Bf r.q (ThrWidth.T a r four L target))+3)+3)+1+(1+1+(2*2^(thrLive r L)ᶜ.card+2)))

/-- **THR C3 inside `complete`.** For every row `j` of the THR family, the fixed `maskW thrLoop` runs from `thrBase j`
to `thrBase j` with the family row's own selection mask on the verdict tape, all heads `0`. -/
theorem thr_mask_work (j : Nat)
    (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length) :
    Step (maskW NI thrLoop) (thrMaskCost a r four L target) (fun _ => 0)
      (thrBase a r four L target NI pub init rcp C cC hF j) (fun _ => 0)
      (Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (loopPort NI vL)
        (PCJ45bee56da9f34d5a_SelectionWord.gridWord (thrLive r L) (thrLive r L)ᶜ.card (half_sum _)
          (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows[j].select)) := by
  obtain ⟨k, hrow, hloop, hc6, _⟩ := thr_base_masters a r four L target NI pub init rcp C cC hF j hj
  have hM := thr_row_mask a r four L target (KeyTop.RT a r four L target) (thrR_le_res _ _) k []
  simp only [List.nil_append] at hM
  rw [← hrow]
  refine mask_work NI (thrLive r L) (thrLive r L)ᶜ.card (KeyTop.RT a r four L target) (loopCl r.q) (loopDl r.q)
    (thrMasters a r four L target (KeyTop.RT a r four L target) k) _ (PCJ45bee56da9f34d5a_SelectionWord.gridWord_length _ _ _ _) _ _
    hM _ (fun i => ?_)
  unfold lslots localT
  rcases split2 i with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rw [Fin.addCases_left, Fin.addCases_left, hloop]; rfl
  · rw [Fin.addCases_right, Fin.addCases_right, hc6]

end Thr

end
end RowsConstruction.CompleteWork
