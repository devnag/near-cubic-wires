import Proof.Assembly.Best
import Proof.Assembly.Clear
import Proof.Assembly.Copy
import Proof.Assembly.Init
import Proof.Assembly.Reset

/-! The single fixed cyclic-mask program. Every runtime input enters on the
four accepted source/driver tapes; all branch choices are made by actual scans. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Program
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def single {t : Nat} (write : Fin t → Option Bool) (move : Fin t → HeadMove) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 1
  rule := fun state _ => if state.val = 0 then some ⟨1,write,move⟩ else none

theorem single_run {t : Nat} (write : Fin t → Option Bool) (move : Fin t → HeadMove)
    (heads : Fin t → Nat) (tapes : Fin t → List Bool) :
    ∃ r, runFrom (single write move) 1 ⟨0,heads,tapes⟩ = some r ∧
      r.final = applyAction ⟨0,heads,tapes⟩ ⟨1,write,move⟩ ∧ r.steps = 1 := by
  exact (Timed.single (by rfl) (show step (single write move) ⟨0,heads,tapes⟩ =
    some (applyAction ⟨0,heads,tapes⟩ ⟨1,write,move⟩) by rfl)).run (by rfl)

-- Body ports: source,q,K,m,winner,double,dummy0,dummy1,candidate,hit,cur,best,log.
-- The outer q driver is the additional fourteenth port.
def initSlots : Fin 8 → Fin 14 := ![1,2,5,4,6,7,13,3]
def resetSlots : Fin 10 → Fin 13 := ![0,6,7,5,8,9,10,1,3,12]
def compareSlots : Fin 2 → Fin 13 := ![8,11]
def copySlots : Fin 3 → Fin 13 := ![1,5,4]
def clearSlots : Fin 1 → Fin 13 := ![8]

theorem initSlots_injective : Function.Injective initSlots := by decide
theorem resetSlots_injective : Function.Injective resetSlots := by decide
theorem compareSlots_injective : Function.Injective compareSlots := by decide
theorem copySlots_injective : Function.Injective copySlots := by decide
theorem clearSlots_injective : Function.Injective clearSlots := by decide

def setup : Machine 14 2 := single
  (fun i => if i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 then some false else none)
  (fun i => if i.val=1 ∨ i.val=8 ∨ i.val=11 then .right else .stay)
def position : Machine 13 2 := single (fun _ => none)
  (fun i => if i.val=8 then .right else .stay)
def shift : Machine 13 2 := single (fun _ => none)
  (fun i => if i.val=5 ∨ i.val=6 ∨ i.val=7 then .left else .stay)

def sizes : Fin 5 → Nat := ![7,3,3,3,2]
noncomputable def parts : (i : Fin 5) → Machine 13 (sizes i)
  | ⟨0,_⟩ => RecoveryFocus.machine compareSlots CompareMachine.machine
  | ⟨1,_⟩ => RecoveryFocus.machine compareSlots Best.machine
  | ⟨2,_⟩ => RecoveryFocus.machine copySlots Copy.machine
  | ⟨3,_⟩ => RecoveryFocus.machine clearSlots Clear.machine
  | ⟨4,_⟩ => shift
  | ⟨i+5,hi⟩ => False.elim (by omega)

def next (i : Fin 5) (state : Fin (sizes i)) (_ : Fin 13 → Bool) : Option (Fin 5) :=
  if i.val=0 then (if state.val=6 then some 1 else some 3)
  else if i.val=1 then some 2
  else if i.val=2 then some 3
  else if i.val=3 then some 4
  else none

noncomputable def decision := RecoveryCalls.machine sizes parts 0 next
noncomputable def body := Composition.machine (RecoveryFocus.machine resetSlots Reset.machine)
  (Composition.machine position decision)
noncomputable def outer := CloseoutRowsDegreeLoop.machine body
noncomputable def machine := Composition.machine (RecoveryFocus.machine initSlots Init.machine)
  (Composition.machine setup outer)

end PCJ93d4cfe17dc847a3.Program
