import Proof.SourceAssembly.MaskLoad

/-! The actual mask producer needs only one existing paid outer rewind.
The sole construction input remains a uniform machine with its complete run
and exact q-bit output, from precisely the accepted source-produced bank. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace PCJ93d4cfe17dc847a3
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open PCJc4297ab269d8423a_Source

structure RawProducer where
  work : Nat
  states : Nat
  machine : Machine (5+work) states
  coefficient : Nat
  degree : Nat
  correct : ∀ d : MaskData, ∃ r,
    run machine (maskBudget coefficient degree d) (d.input work) = some r ∧
    r.final.tapes ⟨4,by omega⟩ = d.word

def RawConstruction : Prop := ∃ (_ : RawProducer), True

theorem input_extend (d : MaskData) (work : Nat) :
    d.input (work+1) =
      Fin.addCases (m := 5+work) (n := 1) (d.input work) (fun _ => []) := by
  funext i
  refine Fin.addCases (m := 5+work) (n := 1) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left, MaskData.input, Fin.val_castAdd]
    split_ifs <;> rfl
  · have h1 : 5+work ≠ 1 := by omega
    have h2 : 5+work ≠ 2 := by omega
    have h3 : 5+work ≠ 3 := by omega
    simp [MaskData.input, h1, h2, h3]

theorem budget_reset (coefficient degree : Nat) (d : MaskData) :
    2 * maskBudget coefficient degree d + 2 ≤
      maskBudget (2*coefficient+2) degree d := by
  have hbase : 1 ≤ (d.q+d.K+d.m+d.supportWord.length+1)^degree := by
    have hpos : 0 < (d.q+d.K+d.m+d.supportWord.length+1)^degree := by positivity
    omega
  unfold maskBudget
  nlinarith

theorem parent (raw : RawConstruction) : MaskConstruction := by
  obtain ⟨p,_⟩ := raw
  refine ⟨{ work := p.work+1
            states := p.states+2
            machine := Rewind.machine p.machine
            coefficient := 2*p.coefficient+2
            degree := p.degree
            positive := by omega
            correct := ?_ }, trivial⟩
  intro d
  obtain ⟨source,hr,ho⟩ := p.correct d
  have hs := runFrom_steps_le p.machine (maskBudget p.coefficient p.degree d)
    _ source hr
  obtain ⟨result,hrun,hout,hheads,_,_⟩ := Rewind.reset_run p.machine
    (maskBudget p.coefficient p.degree d) (d.input p.work) source hr
  have hrun' : run (Rewind.machine p.machine) (2*source.steps+2)
      (d.input (p.work+1)) = some result := by
    rw [input_extend]
    exact hrun
  have hbound : 2*source.steps+2 ≤
      maskBudget (2*p.coefficient+2) p.degree d := by
    calc
      2*source.steps+2 ≤ 2*maskBudget p.coefficient p.degree d+2 := by omega
      _ ≤ maskBudget (2*p.coefficient+2) p.degree d := budget_reset _ _ _
  refine ⟨result.final.tapes,
    (Step.of_run hrun' (funext hheads) rfl).enlarge hbound, ?_⟩
  exact (hout ⟨4,by omega⟩).trans ho

end PCJ93d4cfe17dc847a3
