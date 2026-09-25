import Proof.Packets.PacketsXVectorNumericArena
import Proof.Packets.UnaryAddCount

/-! The one-time terminal-to-delta literal-population change is an executed
copy, counted addition, cursor return, and scratch clear. Only master184
changes from population to twice population. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def pairHeads := Function.update (Function.update heads 184 1) 284 1
def pairUp := Composition.machine (PhysicalIndexReload.move (184 : Fin 299) .right)
  (PhysicalIndexReload.move (284 : Fin 299) .right)
def pairDown := Composition.machine (PhysicalIndexReload.move (284 : Fin 299) .left)
  (PhysicalIndexReload.move (184 : Fin 299) .left)
def addSlots : Fin 2→Fin 299 := ![184,284]
def addCounts := RecoveryFocus.machine addSlots UnaryAddCount.machine
def phaseDouble := Composition.machine (PhysicalCopyInto.machine (31 : Fin 299) 184 284)
  (Composition.machine pairUp (Composition.machine addCounts
    (Composition.machine pairDown (PhysicalCopyInto.machine (31 : Fin 299) 0 284))))

theorem pair_up_run (A : Fin 299→List Bool) : Step pairUp 3 heads A pairHeads A := by
  have first:=PhysicalIndexReload.move_run (184 : Fin 299) .right heads A
  change Step _ 1 heads A (Function.update heads 184 1) A at first
  have last:=PhysicalIndexReload.move_run (284 : Fin 299) .right (Function.update heads 184 1) A
  change Step _ 1 (Function.update heads 184 1) A pairHeads A at last
  exact first.seq last

theorem pair_down_run (A : Fin 299→List Bool) : Step pairDown 3 pairHeads A heads A := by
  have first:=PhysicalIndexReload.move_run (284 : Fin 299) .left pairHeads A
  have last:=PhysicalIndexReload.move_run (184 : Fin 299) .left
    (Function.update pairHeads 284 0) A
  simp only [pairHeads,Function.update_self,HeadMove.apply] at first
  have last' : Step (PhysicalIndexReload.move (184 : Fin 299) .left) 1
      (Function.update pairHeads 284 0) A heads A := by
    apply last.congr _ rfl
    funext i
    by_cases h184:i=184
    · subst i;rfl
    by_cases h284:i=284
    · subst i;rfl
    simp [pairHeads,Function.update,h184,h284]
  exact first.seq last'

theorem double_run (R M : Nat) (A : Fin 299→List Bool)
    (hw : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (hm : A 184=ZeroPadding.pad R (CompareMachine.word M))
    (hs : A 284=List.replicate R false) (hr : 2*M+1≤R) :
    Step phaseDouble (4*R+UnaryAddCount.budget M M+14) heads A heads
      (Function.update A 184 (ZeroPadding.pad R (CompareMachine.word (2*M)))) := by
  let A1:=Function.update A 284 (A 184)
  let A2:=Function.update A1 184 (ZeroPadding.pad R (CompareMachine.word (2*M)))
  have copied:=PhysicalCopyInto.run R (31 : Fin 299) 184 284 (by decide) (by decide) (by decide)
    heads A rfl rfl rfl hw (by simp [hm,ZeroPadding.pad_length,CompareMachine.word];omega)
    (by rw [hs,List.length_replicate])
  have added : Step addCounts (UnaryAddCount.budget M M) pairHeads A1 pairHeads A2 := by
    apply PhysicalFocusBoundary.focus (UnaryAddCount.run R M M) addSlots (by decide)
      pairHeads pairHeads A1 A2
    · intro j;fin_cases j <;>rfl
    · intro j;fin_cases j <;>simpa [A1,addSlots,Function.update] using hm.symm
    · intro j;fin_cases j <;>rfl
    · intro j;fin_cases j
      · simp [A2,addSlots,Function.update,show M+M=2*M by omega]
      · simpa [A2,A1,addSlots,Function.update] using hm.symm
    · intro i away
      have h184:i≠184 := by intro he;exact away 0 he.symm
      exact ⟨rfl,by simp only [A2,Function.update_of_ne h184]⟩
  have cleared:=PhysicalCopyInto.run R (31 : Fin 299) 0 284 (by decide) (by decide) (by decide)
    heads A2 rfl rfl rfl (by simpa [A2,A1,Function.update] using hw)
    (by simp [A2,A1,Function.update,hz])
    (by simp [A2,A1,Function.update,hm,ZeroPadding.pad_length,CompareMachine.word];omega)
  have out : Function.update A2 284 (A2 0)=
      Function.update A 184 (ZeroPadding.pad R (CompareMachine.word (2*M))) := by
    funext i
    by_cases h184:i=184
    · subst i;simp [A2,A1,Function.update]
    by_cases h284:i=284
    · subst i;simp [A2,A1,Function.update,hz,hs]
    simp [A2,A1,Function.update,h184,h284]
  have whole:=copied.seq ((pair_up_run A1).seq (added.seq ((pair_down_run A2).seq (cleared.congr rfl out))))
  have hf : (2*R+2)+1+(3+1+(UnaryAddCount.budget M M+1+(3+1+(2*R+2))))=
      4*R+UnaryAddCount.budget M M+14 := by omega
  rw [hf] at whole;exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
