import Proof.Rows.HeaderBudget

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_Constants
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound

/-- Outer marks for one zero or one bit in an inner binary frame. -/
def zeroBlock : List Bool := [true,true,true,false]
def oneBlock : List Bool := [true,true,true,true]
def zeros (n : Nat) : List Bool := (List.replicate n zeroBlock).flatten

def blocks (phase : Nat) : Fin 11 → List Bool :=
  if phase=0 then
    ![[],[],[],[],[],[],[],zeros 14,zeros 14,oneBlock++zeros 13,oneBlock++zeros 5]
  else if phase=2 then
    ![[],[true,true],[],[],[],[],[],zeros 4,zeros 4,zeros 4,zeros 2]
  else if phase=4 then
    ![[true,true],[],[],[],[],[],[],zeros 4,zeros 4,zeros 4,zeros 2]
  else if phase=6 then
    ![[],[],[true,false,false],[],[],[],[true,false,false],[],[],[],[]]
  else if phase=7 then
    ![[],[],[true,true,false],[],[],[],[true,true,false],[],[],[],[]]
  else if phase=9 then
    ![[],[],[],[],[],[true,true],[],zeros 2,zeros 2,zeros 2,zeros 1]
  else if phase=11 then
    ![[],[],[],[true,true],[true,false],[],[],[],[],[],[]]
  else if phase=12 then
    ![[false],[false],[],[false],[false],[false],[],
      [true,false,false],[true,false,false],[true,false,false],[true,false,false]]
  else fun _=>[]

def width (phase : Nat) : Nat :=
  if phase=0 then 56 else if phase=2 ∨ phase=4 then 16
  else if phase=9 then 8 else if phase=11 then 2 else 3

def after (phase : Nat) : Fin 798 :=
  if phase=0 ∨ phase=2 then 57 else if phase=4 then 285
  else if phase=6 ∨ phase=7 then 456 else if phase=9 then 456
  else if phase=11 then 570 else 741

def sourceMove (phase : Nat) : Fin 4 → HeadMove :=
  if phase=0 ∨ phase=4 then ![.stay,.right,.stay,.stay]
  else if phase=2 then ![.right,.stay,.stay,.stay]
  else if phase=6 ∨ phase=7 ∨ phase=9 then ![.stay,.stay,.right,.stay]
  else if phase=11 then ![.stay,.stay,.stay,.right]
  else fun _=>.stay

def emit (phase k : Nat) (last : Bool) (target : Fin 798) : Action 15 798 where
  nextControl := target
  write := fun j=>Fin.addCases (m:=4) (n:=11)
    (fun _ : Fin 4 => (none : Option Bool)) (fun i : Fin 11 => (blocks phase i)[k]?) j
  move := fun j=>Fin.addCases (m:=4) (n:=11)
    (fun i : Fin 4 => if last then sourceMove phase i else HeadMove.stay)
    (fun i : Fin 11 => if k < (blocks phase i).length then HeadMove.right else HeadMove.stay) j

def jump (target : Fin 798) (moves : Fin 4 → HeadMove := fun _=>.stay) : Action 15 798 :=
  ⟨target,fun _=>none,fun j=>Fin.addCases (m:=4) (n:=11) moves (fun _ : Fin 11 => HeadMove.stay) j⟩

/-- Four retained drivers are p, the sentinel n-template, sentinel Q-word,
and C. The eleven outputs are d,p,odd,C-ones,C-zeros,Q,odd,v0,v0,v1,b1.
The n pass emits once per pair, including a final odd mark. -/
def raw : Machine 15 798 where
  descriptionBits := 0
  start := 0
  halted := fun s=>s.val==741
  rule := fun s bits=>
    let phase := s.val/57
    let k := s.val%57
    if phase=1 then some (jump (if bits 0 then 114 else 171))
    else if phase=3 then some (jump (if bits 1 then 228 else 342))
    else if phase=5 then some (if bits 1 then jump 171 ![.stay,.right,.stay,.stay] else jump 399)
    else if phase=8 then some (jump (if bits 2 then 513 else 570))
    else if phase=10 then some (jump (if bits 3 then 627 else 684))
    else if hp : phase < 13 then
      if k+1 < width phase then
        some (emit phase k false ⟨s.val+1,by
          have h : s.val/57 < 13 := hp
          omega⟩)
      else some (emit phase k true (after phase))
    else none

def machine := Rewind.machine raw

def input (p n Q C : Nat) : Fin 16 → List Bool :=
  fun i=>Fin.addCases (m:=15) (n:=1)
    (fun j=>Fin.addCases (m:=4) (n:=11) (![List.replicate p true,UnaryTemplate.tape n,
      false::List.replicate Q true,List.replicate C true] : Fin 4 → List Bool)
      (fun _ : Fin 11 => ([] : List Bool)) j) (fun _ : Fin 1 => ([] : List Bool)) i

def fields (p n Q C : Nat) : Fin 11 → List Bool :=
  let d := (n+1)/2
  let odd := decide (n%2=1)
  let b := Q+2*d+2*p+6
  let v := 2*b+2
  ![frame (List.replicate d true),frame (List.replicate p true),frame [odd],
    frame (List.replicate C true),frame (List.replicate C false),
    frame (List.replicate Q true),frame [odd],
    frame (frame (SignedSortKey.binary v 0)),frame (frame (SignedSortKey.binary v 0)),
    frame (frame (SignedSortKey.binary v 1)),frame (frame (SignedSortKey.binary b 1))]

end PCJ45bee56da9f34d5a_Constants
