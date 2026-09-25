import Proof.CaseAnalysis.FinalWordEngines

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10FirstPhaseEntry

open NearCubicWires.ExtDecompositionBatch RecoveryRootRound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/- The selected v3 first entry: two copies and two fixed zero-count words.
   Original width218 and nine fresh cells come from AdmittedEntry.run.
   The paid run keeps its actual installed output and every off-map cell. -/

noncomputable def localMachine :=
  Composition.machine
    (RecoveryFocus.machine (![0,1,2,3] : Fin 4 → Fin 10) ClockUnarySum.machine)
    (Composition.machine
      (RecoveryFocus.machine (![0,1,4,5] : Fin 4 → Fin 10) ClockUnarySum.machine)
      (Composition.machine
        (RecoveryFocus.machine (![6,7] : Fin 2 → Fin 10) (HierarchyFixedWord.machine [false]))
        (RecoveryFocus.machine (![8,9] : Fin 2 → Fin 10) (HierarchyFixedWord.machine [false]))))

def input (b : Nat) : Fin 10 → List Bool :=
  ![List.replicate b true,[],[],[],[],[],[],[],[],[]]

theorem local_run (b : Nat) :
    ∃ A : Fin 10 → List Bool,
      Step localMachine (4*b+23) (fun _ => 0) (input b) (fun _ => 0) A ∧
      A 0=List.replicate b true ∧ A 1=[] ∧
      A 2=List.replicate b true ∧ A 4=List.replicate b true ∧
      A 6=[false] ∧ A 8=[false] := by
  obtain ⟨H1,A1,r1,z1,w10,e11,w12,f1⟩ := CloseoutFinalC10WordEngines.copy_dock b
    (![0,1,2,3] : Fin 4 → Fin 10) (by decide) (fun _ => 0) (input b)
    (fun _ => rfl) rfl rfl rfl rfl
  obtain ⟨H2,A2,r2,z2,w20,e21,w24,f2⟩ := CloseoutFinalC10WordEngines.copy_dock b
    (![0,1,4,5] : Fin 4 → Fin 10) (by decide) H1 A1 z1 w10 e11
    ((f1 4 (by decide)).trans rfl) ((f1 5 (by decide)).trans rfl)
  obtain ⟨H3,A3,r3,z3,c36,f3⟩ := CloseoutFinalC10WordEngines.fixedWord_dock [false]
    (![6,7] : Fin 2 → Fin 10) (by decide) H2 A2 z2
    ((f2 6 (by decide)).trans ((f1 6 (by decide)).trans rfl))
    ((f2 7 (by decide)).trans ((f1 7 (by decide)).trans rfl))
  obtain ⟨H4,A4,r4,z4,c48,f4⟩ := CloseoutFinalC10WordEngines.fixedWord_dock [false]
    (![8,9] : Fin 2 → Fin 10) (by decide) H3 A3 z3
    ((f3 8 (by decide)).trans ((f2 8 (by decide)).trans ((f1 8 (by decide)).trans rfl)))
    ((f3 9 (by decide)).trans ((f2 9 (by decide)).trans ((f1 9 (by decide)).trans rfl)))
  have joined := r1.seq (r2.seq (r3.seq r4))
  have time : (2*(b+0)+6)+1+((2*(b+0)+6)+1+
      ((2*[false].length+2)+1+(2*[false].length+2)))=4*b+23 := by
    simp only [List.length_cons,List.length_nil]
    omega
  rw [time] at joined
  refine ⟨A4,joined.congr (funext z4) rfl,?_,?_,?_,?_,?_,c48⟩
  · exact (f4 0 (by decide)).trans ((f3 0 (by decide)).trans w20)
  · exact (f4 1 (by decide)).trans ((f3 1 (by decide)).trans e21)
  · exact (f4 2 (by decide)).trans ((f3 2 (by decide)).trans ((f2 2 (by decide)).trans w12))
  · exact (f4 4 (by decide)).trans ((f3 4 (by decide)).trans w24)
  · exact (f4 6 (by decide)).trans c36

def firstSlots (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B) : Fin 10 → Fin B :=
  ![⟨218,by omega⟩,⟨L+135,by omega⟩,⟨L+817,by omega⟩,⟨L+136,by omega⟩,
    ⟨L+1095,by omega⟩,⟨L+137,by omega⟩,⟨L+689,by omega⟩,⟨L+124,by omega⟩,
    ⟨L+967,by omega⟩,⟨L+125,by omega⟩]

theorem slots_injective (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B) :
    Function.Injective (firstSlots L B hL hSpace) := by
  intro i j hij
  have h := congrArg Fin.val hij
  clear hij
  fin_cases i <;> fin_cases j <;> norm_num [firstSlots] at h
  all_goals first | rfl | omega

noncomputable def machine (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B) :=
  RecoveryFocus.machine (firstSlots L B hL hSpace) localMachine

end NearCubicWires.RepairOrdinary.CloseoutFinalC10FirstPhaseEntry
