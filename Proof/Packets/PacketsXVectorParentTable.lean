import Proof.Packets.PacketsXVectorWorkerCommitNat

/-! Exact prefix of the materialized parent vector; replacing its next slot
preserves all already constructed coordinates and all remaining zero slots. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

def parentTable (N : Nat) (answer : Nat→Ring.Poly Nat) (done : Nat) : List (Ring.Poly Nat) :=
  List.ofFn (fun j : Fin N=>if j.val<done then answer j.val else [])

theorem parentTable_length (N : Nat) (answer : Nat→Ring.Poly Nat) (done : Nat) :
    (parentTable N answer done).length=N := List.length_ofFn

theorem parentTable_zero (N : Nat) (answer : Nat→Ring.Poly Nat) :
    parentTable N answer 0=List.replicate N [] := by
  simp [parentTable]

theorem parentTable_full (N : Nat) (answer : Nat→Ring.Poly Nat) :
    parentTable N answer N=List.ofFn (fun j : Fin N=>answer j.val) := by
  simp [parentTable]

theorem parentTable_set (N : Nat) (answer : Nat→Ring.Poly Nat) (i : Fin N) :
    (parentTable N answer i.val).set i.val (answer i.val)=parentTable N answer (i.val+1) := by
  apply List.ext_getElem
  · simp only [List.length_set,parentTable_length]
  · intro j hleft hright
    have hj:j<N := by simpa only [parentTable_length] using hright
    simp only [parentTable,List.getElem_set,List.getElem_ofFn]
    by_cases he:j=i.val
    · subst j;simp
    · have he':i.val≠j:=Ne.symm he
      simp only [he',if_false]
      split_ifs <;>first | rfl | omega

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
