import Proof.Packets.AddressedAtomProgram
import Proof.Packets.PhysicalRepeatStep

/-! Every active iteration of the fixed dense-table loop executes the
checked indexed atom worker. Its count, keys, source cursors and all table
bytes are the exact states of AddressedAtomProgram. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomProgram
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair word cacheWord)
open PacketVector (Packet)

def H (coding : Nat→Nat) (cs : List Pair) (j : Nat) := NativeIndexedAtom.heads 0 (codePrefix coding cs j).length
def A (C R : Nat) (coding : Nat→Nat) (cs : List Pair) (initial : List Packet) (j : Nat) :=
  NativeIndexedAtom.data C R (cacheWord cs) (codes coding cs)
    (PacketVector.bank R (table C coding cs initial j)) (index cs j)
def bodyBudget (C R : Nat) := 128*(C+1)*(R+1)

theorem iteration_run (C R : Nat) (coding : Nat→Nat) (cs : List Pair) (initial : List Packet)
    (hR : C+2≤R) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,coding i<C)
    (hcache : (cacheWord cs).length≤R) (hinit : initial.length=C)
    (hinits : ∀P∈initial,PacketVector.Fits R P)
    (hcopy : ∀p∈cs,CloseoutRowsRawPairCopy.budget p≤R+3)
    (hfits : ∀p∈cs,∀m∈p.1++p.2,∀i∈m,i<C)
    (hdata : ∀p∈cs,∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤R)
    (hfuel : ∀p∈cs,NativeNormalized.budget C (p.1++p.2)+3≤R)
    (j : Nat) (hj : j<cs.length) :
    Step NativeIndexedAtom.machine (bodyBudget C R) (H coding cs j) (A C R coding cs initial j)
      (H coding cs (j+1)) (A C R coding cs initial (j+1)) := by
  let i:=index cs j
  let c:=code coding cs j
  let p:=atom cs j
  let ps:=table C coding cs initial j
  have hi : i<cs.length := index_lt cs j hj
  have hp : p∈cs := atom_mem cs j hj
  have hc : c<C := hcodes i hi
  have hpslen : ps.length=C := (table_length C coding cs initial j).trans hinit
  have hci : c<ps.length := by omega
  have hanswer : ∀p∈cs,PacketVector.Fits R (NativeAtomStore.answer C p) := by
    intro p hp
    exact NativeNormalized.output_fits C R (p.1++p.2) (hfits p hp) (hdata p hp) (hfuel p hp)
  have hps : ∀P∈ps,PacketVector.Fits R P := table_fits C R coding cs initial hinits hanswer j (by omega)
  have hold:=hps ps[c] (List.getElem_mem hci)
  have hout:=hanswer p hp
  have ht : (cs.take i).length=i := by simp [List.length_take,Nat.min_eq_left hi.le]
  have source : cacheWord (cs.take i)++word p++cacheWord (cs.drop (i+1))=cacheWord cs := raw_split cs j hj
  have hsourceLength:=congrArg List.length source
  simp only [List.length_append] at hsourceLength
  have hshort : (cacheWord (cs.take i)).length+(word p).length≤R := by omega
  have codeSource : codePrefix coding cs j++NativeLiteralCode.word c++suffix coding cs j=codes coding cs := code_split coding cs j hj
  have bankSource : PacketVector.bank R (ps.take c)++PacketVector.payload R ps[c]++
      PacketVector.count R ps[c]++PacketVector.bank R (ps.drop (c+1))=PacketVector.bank R ps :=
    (PacketVector.bank_split R ps ⟨c,hci⟩).symm
  have bankTarget : NativeAtomStore.updatedBank C R p (PacketVector.bank R (ps.take c))
      (PacketVector.bank R (ps.drop (c+1)))=PacketVector.bank R (ps.set c (NativeAtomStore.answer C p)) := by
    rw [PacketVector.bank_set R ps c _ hci]
    rfl
  have hpre : (PacketVector.bank R (ps.take c)).length=2*c*R := by
    rw [PacketVector.bank_length R _ (fun P hP=>hps P (List.mem_of_mem_take hP)),List.length_take,
      Nat.min_eq_left hci.le]
  have actual:=NativeIndexedAtom.run C R c (cs.take i) (cacheWord (cs.drop (i+1)))
    (codePrefix coding cs j) (suffix coding cs j) (PacketVector.bank R (ps.take c))
    (PacketVector.payload R ps[c]) (PacketVector.count R ps[c]) (PacketVector.bank R (ps.drop (c+1)))
    p (by omega) (by rw [ht];omega) (hcopy p hp) (hfits p hp) (hdata p hp) (hfuel p hp)
    hpre (PacketVector.payload_length hold) (PacketVector.count_length hold)
    hout.1 (by simpa [CompareMachine.word] using hout.2) (by omega) hshort
  have cost:=NativeIndexedAtom.budget_le C R c (cs.take i) p (hcopy p hp) (hfuel p hp)
    (by omega) (by rw [ht];omega) hc.le
  have bounded:=actual.enlarge cost
  rw [source,codeSource,bankSource,bankTarget,ht] at bounded
  have nextIndex : i-1=index cs (j+1) := by unfold i index;omega
  have nextCursor : (codePrefix coding cs j).length+c+6=(codePrefix coding cs (j+1)).length :=
    (prefix_length_succ coding cs j hj).symm
  rw [nextIndex,nextCursor] at bounded
  exact bounded

end PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomProgram
