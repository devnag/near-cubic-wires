import Proof.CaseAnalysis.RowsModeElementaryReset

/-! The original C driver clears the elementary work bank and its recording
log. The output, four numeric masters and all unrelated heads are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryClear
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def saved (i : Fin 45) : Fin 52:=if h:i.val<44 then ⟨i.val,by omega⟩ else 45
def slots : Fin 47→Fin 52:=Fin.addCases (m:=45) (n:=2) (motive:=fun _=>Fin 52) saved ![50,51]
theorem injective : Function.Injective slots:=by decide
noncomputable def machine:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 45)
def output (A : Fin 52→List Bool) (C : Nat) (i : Fin 52):=
  if i.val<44 ∨ i=45 then List.replicate C false else A i

theorem clear_run (H : Fin 52→Nat) (A : Fin 52→List Bool) (C : Nat)
    (hH : ∀ j,H (slots j)=0) (hT : A 50=List.replicate C true)
    (hZ : A 51=List.replicate (C+1) false) (hfit : ∀ j,(A (saved j)).length≤C) :
    ∃ r,runFrom machine (2*C+4) ⟨machine.start,H,A⟩=some r ∧
      r.steps=2*C+4 ∧ r.final.heads=H ∧ r.final.tapes=output A C := by
  let backing : Fin 45→List Bool:=fun j=>A (saved j)
  have hA:∀ j,A (slots j)=
      (Fin.addCases (m:=46) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=45) (n:=1) (motive:=fun _=>List Bool) backing (fun _=>List.replicate C true))
        (fun _=>List.replicate (C+1) false)) j:=by
    intro j;fin_cases j <;> first | rfl | exact hT | exact hZ
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryScratchErase.erase_ready C (C+1) backing hfit).focus_at
    slots injective H A hA hH
  have he:install slots A
      (Fin.addCases (m:=46) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=45) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=output A C:=by
    apply HierarchyAllocation.install_eq slots injective
    · intro j;fin_cases j
      all_goals first | rfl | exact hT |
        (change A 51=List.replicate (max (C+1) (C+1)) false;rw [max_self];exact hZ)
    · intro i hi
      have hn:¬(i.val<44 ∨ i=45):=by
        rintro (hl|rfl)
        · exact hi ((⟨i.val,by omega⟩ : Fin 45).castAdd 2) (by
            apply Fin.ext
            simp [slots,saved,Fin.addCases,hl,show i.val<45 by omega])
        · exact hi ((44 : Fin 45).castAdd 2) rfl
      simp only [output,hn,if_false]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryClear
