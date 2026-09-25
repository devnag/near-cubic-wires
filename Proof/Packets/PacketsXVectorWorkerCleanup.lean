import Proof.Packets.PacketsXVectorWorkerArena

/-! Paid cleanup of all seventeen numeric scratch ports. The metadata outputs
and retained masters are outside the erased range. The same physical raw-R
and log backing are returned, so the operation is reusable. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def scratch (j : Fin 17) : Fin 296 := ⟨264+j.val,by omega⟩
def eraseSlots : Fin 19→Fin 296 := Fin.addCases (m:=17) (n:=2) (motive:=fun _=>Fin 296)
  scratch (![32,33])
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 17)
def cleared (R : Nat) (A : Fin 296→List Bool) (i : Fin 296) : List Bool :=
  if 264 ≤ i.val ∧ i.val < 281 then List.replicate R false else A i

theorem scratch_head (j : Fin 17) : heads (scratch j)=0 := by
  simp only [heads,scratch,Fin.ext_iff]
  split <;>omega

theorem erase_injective : Function.Injective eraseSlots := by decide

theorem erase_run (R : Nat) (A : Fin 296→List Bool)
    (ha : ∀j,(A (scratch j)).length≤R)
    (hraw : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false) :
    Step erase (2*R+4) heads A heads (cleared R A) := by
  have small:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3) (fun j=>A (scratch j)) ha)
  apply PhysicalFocusBoundary.focus small eraseSlots erase_injective heads heads A (cleared R A)
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>first | rfl | exact hraw.symm | exact hlog.symm
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>
      simp [cleared,eraseSlots,scratch,Fin.addCases,hraw,hlog,
        Nat.max_eq_left (by omega : R+1≤R+3)]
  · intro i away
    refine ⟨rfl,?_⟩
    have hn : ¬ (264 ≤ i.val ∧ i.val < 281) := by
      intro h
      let j : Fin 17:=⟨i.val-264,by omega⟩
      apply away (j.castAdd 2)
      apply Fin.ext
      rw [show eraseSlots (j.castAdd 2)=scratch j from Fin.addCases_left j]
      dsimp [scratch,j]
      omega
    simp only [cleared,if_neg hn]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
