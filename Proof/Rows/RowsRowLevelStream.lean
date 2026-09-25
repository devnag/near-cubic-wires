import Proof.Rows.RowsRowLevelHeaderClear
import Proof.Rows.HeaderBudget

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsRowLevel
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
noncomputable section

/-- The scratch erase: ports `v 4`, `v 5`, then the driver `v 1` and the log `v 2`. -/
def streamErase {T : Nat} (v : Fin 9 → Fin T) : Fin (2+1+1) → Fin T :=
  Fin.addCases (m:=2+1) (n:=1) (Fin.addCases (m:=2) (n:=1) ![v 4,v 5] (fun _ : Fin 1=>v 1))
    (fun _ : Fin 1=>v 2)

/-- The fixed C1 machine for a fixed port assignment `v`. -/
def streamMachine {T : Nat} (v : Fin 9 → Fin T) :=
  Composition.machine (RecoveryFocus.machine v PCJ45bee56da9f34d5a_HeaderField.machine)
    (RecoveryFocus.machine (streamErase v) (RecoveryScratchErase.resetMachine 2))

theorem streamErase_eq {T : Nat} (v : Fin 9 → Fin T) : streamErase v=v ∘ ![4,5,1,2] := by
  funext i
  refine Fin.addCases (m:=2+1) (n:=1) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=2) (n:=1) (fun i=>?_) (fun i=>?_) i
    · fin_cases i <;> rfl
    · fin_cases i
      rfl
  · fin_cases i
    rfl

theorem streamErase_injective {T : Nat} (v : Fin 9 → Fin T) (hv : Function.Injective v) :
    Function.Injective (streamErase v) := by
  rw [streamErase_eq]
  exact hv.comp (by decide)

theorem padNil (K : Nat) : ZeroPadding.pad K []=List.replicate K false := by
  simp [ZeroPadding.pad]

/-- The Scan tick log is at most `3*copyCap` long. -/
theorem ticks_le_cap (row : EquationRow.Input) (K : Nat) (fits : 2*(Header.stream row).length+1 ≤ K) :
    Scan.ticks row ≤ 3*K := by
  have h := PCJ45bee56da9f34d5a_HeaderBudget.ticks_le row
  omega

theorem cuts_le_stream (row : EquationRow.Input) : row.cuts.length ≤ (Header.stream row).length := by
  rw [PCJ45bee56da9f34d5a_HeaderBudget.stream_length]
  have hf : 1 ≤ Scan.countFields row := by
    unfold Scan.countFields
    omega
  have h1 : row.cuts.length ≤ row.cuts.length*Scan.countFields row := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left row.cuts.length hf
  have h2 : row.cuts.length*Scan.countFields row ≤
      row.cuts.length*(Scan.countFields row*(2*row.p+3)) := by
    rw [←Nat.mul_assoc]
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (row.cuts.length*Scan.countFields row) (show 1 ≤ 2*row.p+3 by omega)
  omega

/-- **C1, the framed Header stream.** Port assignment `v`: `v 0` the stream port (head at its
end), `v 1`/`v 2` the `copyCap` driver/log, `v 3` the count template, `v 4`, `v 5`, `v 8` blank
`0^K` scratch (any cleared payload ports off the thirteen fields), `v 6` a blank tick log
`0^S` (`ticks ≤ S`), `v 7` the output (field 2's slot, `0^K`). One fixed machine writes
`pad K (frame stream)` on `v 7`, parks the stream head at `0`, and restores every other port. -/
theorem stream_step {T : Nat} (v : Fin 9 → Fin T) (hv : Function.Injective v)
    (row : EquationRow.Input) (K S r0 r3 : Nat)
    (fits : 2*(Header.stream row).length+1 ≤ K) (hS : Scan.ticks row ≤ S)
    (H : Fin T → Nat) (A : Fin T → List Bool)
    (h0 : H (v 0)=(Header.stream row).length) (hz : ∀ i,i≠0 → H (v i)=0)
    (a0 : A (v 0)=ZeroPadding.pad r0 (Header.stream row))
    (a1 : A (v 1)=List.replicate K true) (a2 : A (v 2)=List.replicate (K+1) false)
    (a3 : A (v 3)=ZeroPadding.pad r3 (UnaryTemplate.tape (Scan.countFields row)))
    (a4 : A (v 4)=List.replicate K false) (a5 : A (v 5)=List.replicate K false)
    (a6 : A (v 6)=List.replicate S false) (a7 : A (v 7)=List.replicate K false)
    (a8 : A (v 8)=List.replicate K false) :
    Step (streamMachine v) (PCJ45bee56da9f34d5a_HeaderField.budget row K+1+(2*K+4)) H A
      (dockH v H (fun _=>0)) (Function.update A (v 7) (ZeroPadding.pad K (frame (Header.stream row)))) := by
  classical
  have hs : (Header.stream row).length ≤ K := by omega
  let cap : Fin 9 → Nat := ![r0,0,K+1,r3,K,K,S,K,K]
  have first := (PCJ45bee56da9f34d5a_HeaderField.padded_run row K hs cap).dock v hv H A
    (by
      intro i
      fin_cases i
      · exact h0
      all_goals exact hz _ (by decide))
    (by
      intro i
      fin_cases i
      · exact a0
      · show A (v 1)=ZeroPadding.pad 0 (List.replicate K true)
        rw [a1,ZeroPadding.pad_zero]
      · show A (v 2)=ZeroPadding.pad (K+1) []
        rw [a2,padNil]
      · exact a3
      · show A (v 4)=ZeroPadding.pad K []
        rw [a4,padNil]
      · show A (v 5)=ZeroPadding.pad K []
        rw [a5,padNil]
      · show A (v 6)=ZeroPadding.pad S []
        rw [a6,padNil]
      · show A (v 7)=ZeroPadding.pad K []
        rw [a7,padNil]
      · show A (v 8)=ZeroPadding.pad K []
        rw [a8,padNil])
  -- the intermediate bank
  let B := install v A (fun i=>ZeroPadding.pad (cap i) (PCJ45bee56da9f34d5a_HeaderField.output row K i))
  have hB : ∀ i,B (v i)=ZeroPadding.pad (cap i) (PCJ45bee56da9f34d5a_HeaderField.output row K i) :=
    fun i=>install_slot _ hv _ _ i
  have hei := streamErase_injective v hv
  let back : Fin 2 → List Bool := ![B (v 4),B (v 5)]
  have hback : ∀ i,(back i).length ≤ K := by
    intro i
    fin_cases i
    · change (B (v 4)).length ≤ K
      rw [hB]
      have hc := cuts_le_stream row
      simp [cap,PCJ45bee56da9f34d5a_HeaderField.output,ZeroPadding.pad]
      omega
    · change (B (v 5)).length ≤ K
      rw [hB]
      simp [cap,PCJ45bee56da9f34d5a_HeaderField.output,ZeroPadding.pad]
      omega
  have erase : Step (RecoveryScratchErase.resetMachine 2) (2*K+4) (fun _=>0)
      (PCJ45bee56da9f34d5a_Plan.clearInput K (K+1) back) (fun _=>0)
      (PCJ45bee56da9f34d5a_Plan.clearOutput 2 K (K+1)) := by
    unfold PCJ45bee56da9f34d5a_Plan.clearOutput PCJ45bee56da9f34d5a_Plan.clearInput
    simpa only [Nat.max_self] using Step.of_ready (RecoveryScratchErase.erase_ready K (K+1) back hback)
  have second := erase.dock (streamErase v) hei (dockH v H (fun _=>0)) B
    (by
      intro i
      refine Fin.addCases (m:=2+1) (n:=1) (fun i=>?_) (fun i=>?_) i
      · refine Fin.addCases (m:=2) (n:=1) (fun i=>?_) (fun i=>?_) i
        · fin_cases i <;> exact dockH_slot _ hv _ _ _
        · simp only [streamErase,Fin.addCases_left,Fin.addCases_right]
          exact dockH_slot _ hv _ _ _
      · simp only [streamErase,Fin.addCases_right]
        exact dockH_slot _ hv _ _ _)
    (by
      intro i
      refine Fin.addCases (m:=2+1) (n:=1) (fun i=>?_) (fun i=>?_) i
      · refine Fin.addCases (m:=2) (n:=1) (fun i=>?_) (fun i=>?_) i
        · fin_cases i <;> rfl
        · simp only [streamErase,PCJ45bee56da9f34d5a_Plan.clearInput,Fin.addCases_left,
            Fin.addCases_right]
          rw [hB]
          simp [cap,PCJ45bee56da9f34d5a_HeaderField.output,ZeroPadding.pad]
      · simp only [streamErase,PCJ45bee56da9f34d5a_Plan.clearInput,Fin.addCases_right]
        rw [hB]
        simp [cap,PCJ45bee56da9f34d5a_HeaderField.output,ZeroPadding.pad])
  refine (first.seq second).congr ?_ ?_
  · exact dockH_existing _ _ _ (fun i=>by
      refine Fin.addCases (m:=2+1) (n:=1) (fun i=>?_) (fun i=>?_) i
      · refine Fin.addCases (m:=2) (n:=1) (fun i=>?_) (fun i=>?_) i
        · fin_cases i <;> exact dockH_slot _ hv _ _ _
        · simp only [streamErase,Fin.addCases_left,Fin.addCases_right]
          exact dockH_slot _ hv _ _ _
      · simp only [streamErase,Fin.addCases_right]
        exact dockH_slot _ hv _ _ _)
  · funext x
    have hE : ∀ m,streamErase v m=v ((![4,5,1,2] : Fin 4 → Fin 9) m) := fun m=>by rw [streamErase_eq]; rfl
    by_cases hx7 : x=v 7
    · subst hx7
      rw [Function.update_self,install_other _ _ _ _ (fun m he=>by
        rw [hE] at he
        have := hv he
        fin_cases m <;> simp at this),hB]
      rfl
    · rw [Function.update_of_ne hx7]
      by_cases hs : ∃ m,streamErase v m=x
      · obtain ⟨m,rfl⟩ := hs
        rw [install_slot _ hei,hE]
        fin_cases m
        · show List.replicate K false=A (v 4)
          rw [a4]
        · show List.replicate K false=A (v 5)
          rw [a5]
        · show List.replicate K true=A (v 1)
          rw [a1]
        · show List.replicate (K+1) false=A (v 2)
          rw [a2]
      · rw [install_other _ _ _ _ (fun m he=>hs ⟨m,he⟩)]
        by_cases hvx : ∃ i,v i=x
        · obtain ⟨i,rfl⟩ := hvx
          rw [hB]
          have hno : ∀ m : Fin 4,(![4,5,1,2] : Fin 4 → Fin 9) m≠i := fun m he=>hs ⟨m,by rw [hE,he]⟩
          fin_cases i
          · show ZeroPadding.pad r0 (Header.stream row)=A (v 0)
            rw [a0]
          · exact absurd rfl (hno 2)
          · exact absurd rfl (hno 3)
          · show ZeroPadding.pad r3 (UnaryTemplate.tape (Scan.countFields row))=A (v 3)
            rw [a3]
          · exact absurd rfl (hno 0)
          · exact absurd rfl (hno 1)
          · show ZeroPadding.pad S (List.replicate (Scan.ticks row) false)=A (v 6)
            rw [a6,pad_replicate_false _ _ hS]
          · exact absurd rfl hx7
          · show ZeroPadding.pad K (List.replicate (2*(Header.stream row).length+1) false)=A (v 8)
            rw [a8,pad_replicate_false _ _ fits]
        · exact install_other _ _ _ _ (fun i he=>hvx ⟨i,he⟩)


end
end RowsRowLevel
