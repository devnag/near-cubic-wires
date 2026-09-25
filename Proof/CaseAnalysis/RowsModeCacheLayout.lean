import Proof.CaseAnalysis.RowsModeLiteralScan

/-! Fixed physical cache population layout. The original mask, seed and
level are retained; the actual label and two distinct live counts advance. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Parameters where
  rank : Nat
  level : Nat
  C : Nat
  lower : List Bool
  upper : List Bool
  translation : List Bool
  mask : List Bool
structure State where
  index : Nat
  selectedCount : Nat
  children : Nat
  out : List Bool
  zero : Bool
  sibling : Bool
  child : Bool
  var : Bool
  neg : Bool

def label (p : Parameters) (s : State):=binary (p.rank+1) s.index
def hashWord (p : Parameters) (s : State):=
  CloseoutRowsModeHashLoop.word p.rank p.rank (label p s) p.lower p.upper p.translation

def extras (p : Parameters) (s : State) : Fin 13→List Bool:=
  ![p.mask,List.replicate p.level true,[s.zero],[s.sibling],[s.child],[s.var],[s.neg],
    UnaryTemplate.tape (s.index+1),CompareMachine.word s.selectedCount,s.out,List.replicate p.C true,
    List.replicate (p.C+1) false,CompareMachine.word s.children]
def extraHeads (s : State) (pos : Nat) : Fin 13→Nat:=
  ![s.index,0,0,0,0,pos,0,1,s.selectedCount+1,s.out.length,0,0,s.children+1]
def heads (s : State) (pos : Nat:=0) : Fin 24→Nat:=Fin.addCases (m:=11) (n:=13) (motive:=fun _=>Nat) (fun _=>0) (extraHeads s pos)
def fields (p : Parameters) (s : State) (hashed : Bool):=
  if hashed then CloseoutRowsModeHashFields.after p.rank p.rank p.C (label p s) p.lower p.upper p.translation
  else CloseoutRowsModeHashFields.before p.rank p.rank p.C (label p s) p.lower p.upper p.translation
def data (p : Parameters) (s : State) (hashed : Bool) : Fin 24→List Bool:=
  Fin.addCases (m:=11) (n:=13) (motive:=fun _=>List Bool) (fields p s hashed) (extras p s)

def guarded (p : Parameters) (s : State) : State:=
  let z:=CloseoutRowsModeHashCell.zeroFlag ((hashWord p s).take p.level)
  let b:=readTapeBit (hashWord p s) p.level
  {s with zero:=z,sibling:=z&&b,child:=z&&!b}
def selected (mode : Fin 3) (p : Parameters) (s : State) : State:=
  {s with
    var := CloseoutRowsModeLiteralSelect.varFlag mode s.zero s.sibling s.child (readTapeBit p.mask s.index)
    neg := CloseoutRowsModeLiteralSelect.negative mode s.zero s.sibling s.child
    children := s.children+s.child.toNat}
def pairWord (s : State):=CloseoutRowsRawPairSeek.word (CloseoutRowsModeLiteralPair.pair s.neg s.var s.index)
def emitted (s : State) : State:=
  {s with index:=s.index+1,selectedCount:=s.selectedCount+s.var.toNat,out:=s.out++pairWord s,neg:=s.var}

def guardSlots : Fin 6→Fin 24:=![8,12,13,14,15,10]
def selectSlots : Fin 7→Fin 24:=![13,14,15,11,16,17,23]
def pairSlots : Fin 5→Fin 24:=![16,18,20,19,17]
def labelSlots : Fin 2→Fin 24:=![1,10]
def eraseSlots : Fin 5→Fin 24:=![4,6,8,21,22]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
