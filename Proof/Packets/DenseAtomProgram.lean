import Proof.Packets.NativeIndexedCost
import Proof.Packets.NativeNormalizedCapacity
import Proof.Packets.PacketVectorReplace

/-! Exact states of the descending physical atom-table loop. The index
addresses the original native cache while its Nat.pair code selects the
dense packet entry. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomProgram
open NearCubicWires NearCubicWires.RepairOrdinary
open CloseoutRowsRawPairSeek (Pair word cacheWord)
open PacketVector (Packet)

def index (cs : List Pair) (j : Nat) := cs.length-1-j
def code (tag : Nat) (cs : List Pair) (j : Nat) := Nat.pair tag (index cs j)
def atom (cs : List Pair) (j : Nat) := cs.getD (index cs j) ([],[])
def codeList (tag : Nat) (cs : List Pair) := (List.range cs.length).map (code tag cs)
def codes (tag : Nat) (cs : List Pair) := (codeList tag cs).flatMap NativeLiteralCode.word
def codePrefix (tag : Nat) (cs : List Pair) (j : Nat) := ((codeList tag cs).take j).flatMap NativeLiteralCode.word
def suffix (tag : Nat) (cs : List Pair) (j : Nat) := ((codeList tag cs).drop (j+1)).flatMap NativeLiteralCode.word
def table (C tag : Nat) (cs : List Pair) (initial : List Packet) : Nat→List Packet
  | 0=>initial
  | j+1=>(table C tag cs initial j).set (code tag cs j) (NativeAtomStore.answer C (atom cs j))

theorem index_lt (cs : List Pair) (j : Nat) (hj : j<cs.length) : index cs j<cs.length := by
  unfold index;omega

theorem atom_eq (cs : List Pair) (j : Nat) (hj : j<cs.length) :
    atom cs j=cs[index cs j]'(index_lt cs j hj) := by
  simp [atom,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (index_lt cs j hj)]

theorem atom_mem (cs : List Pair) (j : Nat) (hj : j<cs.length) : atom cs j∈cs := by
  rw [atom_eq cs j hj]
  exact List.getElem_mem _

theorem raw_split (cs : List Pair) (j : Nat) (hj : j<cs.length) :
    cacheWord (cs.take (index cs j))++word (atom cs j)++cacheWord (cs.drop (index cs j+1))=cacheWord cs := by
  have h : cs.take (index cs j)++atom cs j::cs.drop (index cs j+1)=cs := by
    rw [atom_eq cs j hj,List.getElem_cons_drop,List.take_append_drop]
  simpa only [cacheWord,List.flatMap_append,List.flatMap_cons,List.append_assoc] using congrArg cacheWord h

theorem codeList_length (tag : Nat) (cs : List Pair) : (codeList tag cs).length=cs.length := by
  simp [codeList]

theorem codeList_get (tag : Nat) (cs : List Pair) (j : Nat) (hj : j<(codeList tag cs).length) :
    (codeList tag cs)[j]=code tag cs j := by
  simp [codeList]

theorem code_split (tag : Nat) (cs : List Pair) (j : Nat) (hj : j<cs.length) :
    codePrefix tag cs j++NativeLiteralCode.word (code tag cs j)++suffix tag cs j=codes tag cs := by
  have h : (codeList tag cs).take j++code tag cs j::(codeList tag cs).drop (j+1)=codeList tag cs := by
    rw [←codeList_get tag cs j (by simpa only [codeList_length] using hj),
      List.getElem_cons_drop,List.take_append_drop]
  simpa only [codePrefix,suffix,codes,List.flatMap_append,List.flatMap_cons,List.append_assoc] using
    congrArg (List.flatMap NativeLiteralCode.word) h

theorem prefix_succ (tag : Nat) (cs : List Pair) (j : Nat) (hj : j<cs.length) :
    codePrefix tag cs (j+1)=codePrefix tag cs j++NativeLiteralCode.word (code tag cs j) := by
  unfold codePrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [codeList_length] using hj),
    List.flatMap_append,List.flatMap_singleton,codeList_get]

theorem prefix_length_succ (tag : Nat) (cs : List Pair) (j : Nat) (hj : j<cs.length) :
    (codePrefix tag cs (j+1)).length=(codePrefix tag cs j).length+code tag cs j+6 := by
  rw [prefix_succ tag cs j hj]
  simp [NativeLiteralCode.word,Nat.add_assoc]

theorem table_length (C tag : Nat) (cs : List Pair) (initial : List Packet) (j : Nat) :
    (table C tag cs initial j).length=initial.length := by
  induction j with
  | zero=>rfl
  | succ j ih=>simpa only [table,List.length_set] using ih

theorem table_fits (C R tag : Nat) (cs : List Pair) (initial : List Packet)
    (hs : ∀P∈initial,PacketVector.Fits R P)
    (hp : ∀p∈cs,PacketVector.Fits R (NativeAtomStore.answer C p))
    (j : Nat) (hj : j≤cs.length) : ∀P∈table C tag cs initial j,PacketVector.Fits R P := by
  induction j with
  | zero=>exact hs
  | succ j ih=>
    exact PacketVector.fits_set R _ _ _ (ih (by omega)) (hp _ (atom_mem cs j (by omega)))

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomProgram
