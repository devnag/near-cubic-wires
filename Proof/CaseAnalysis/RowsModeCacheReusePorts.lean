import Proof.CaseAnalysis.RowsModeCacheReuseLayout

/-! Small concrete port identities keep the actual erase join compact. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reuse_erase_injective : Function.Injective reuseEraseSlots:=by decide
theorem reuse_erase_heads (out : List Bool) (j : Fin 17) : reuseHeads out (reuseEraseSlots j)=0:=by
  fin_cases j <;> rfl
theorem reuse_erase_fields (p : Parameters) (M R D : Nat) (out : List Bool) (A : Fin 15→List Bool)
    (j : Fin 17) : reuseData p M R D out A (reuseEraseSlots j)=
      Fin.addCases (m:=16) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=15) (n:=1) (motive:=fun _=>List Bool) A (fun _=>List.replicate D true))
        (fun _=>List.replicate (D+1) false) j:=by
  fin_cases j <;> rfl
def reuseMasterSlots : Fin 13→Fin 28:=![0,2,3,5,9,11,12,20,21,24,25,26,27]
def reuseMasters (p : Parameters) (M R D : Nat) (out : List Bool) : Fin 13→List Bool:=
  ![List.replicate p.rank true,p.lower,p.upper,p.translation,CompareMachine.word p.rank,p.mask,
    List.replicate p.level true,out,List.replicate p.C true,CompareMachine.word M,
    List.replicate R false,List.replicate D true,List.replicate (D+1) false]
theorem reuse_master_fields (p : Parameters) (M R D : Nat) (out : List Bool) (A : Fin 15→List Bool)
    (j : Fin 13) : reuseData p M R D out A (reuseMasterSlots j)=reuseMasters p M R D out j:=by
  fin_cases j <;> rfl
theorem reuse_master_exists (i : Fin 28) (h : ∀ j,reuseEraseSlots j≠i) :
    ∃ j,reuseMasterSlots j=i:=by
  have hn (k : Fin 17) : i.val≠(reuseEraseSlots k).val:=fun he=>h k (Fin.ext he.symm)
  have h0 : i.val≠1:=hn 0
  have h1 : i.val≠4:=hn 1
  have h2 : i.val≠6:=hn 2
  have h3 : i.val≠7:=hn 3
  have h4 : i.val≠8:=hn 4
  have h5 : i.val≠10:=hn 5
  have h6 : i.val≠13:=hn 6
  have h7 : i.val≠14:=hn 7
  have h8 : i.val≠15:=hn 8
  have h9 : i.val≠16:=hn 9
  have h10 : i.val≠17:=hn 10
  have h11 : i.val≠18:=hn 11
  have h12 : i.val≠19:=hn 12
  have h13 : i.val≠22:=hn 13
  have h14 : i.val≠23:=hn 14
  have other : i.val=0 ∨ i.val=2 ∨ i.val=3 ∨ i.val=5 ∨ i.val=9 ∨ i.val=11 ∨ i.val=12 ∨
      i.val=20 ∨ i.val=21 ∨ i.val=24 ∨ i.val=25 ∨ i.val=26 ∨ i.val=27:=by omega
  rcases other with he|he|he|he|he|he|he|he|he|he|he|he|he
  · exact ⟨0,Fin.ext he.symm⟩
  · exact ⟨1,Fin.ext he.symm⟩
  · exact ⟨2,Fin.ext he.symm⟩
  · exact ⟨3,Fin.ext he.symm⟩
  · exact ⟨4,Fin.ext he.symm⟩
  · exact ⟨5,Fin.ext he.symm⟩
  · exact ⟨6,Fin.ext he.symm⟩
  · exact ⟨7,Fin.ext he.symm⟩
  · exact ⟨8,Fin.ext he.symm⟩
  · exact ⟨9,Fin.ext he.symm⟩
  · exact ⟨10,Fin.ext he.symm⟩
  · exact ⟨11,Fin.ext he.symm⟩
  · exact ⟨12,Fin.ext he.symm⟩
theorem reuse_erase_keep (p : Parameters) (M R D : Nat) (out : List Bool)
    (A B : Fin 15→List Bool) (i : Fin 28) (h : ∀ j,reuseEraseSlots j≠i) :
    reuseData p M R D out B i=reuseData p M R D out A i:=by
  obtain ⟨j,rfl⟩:=reuse_master_exists i h
  rw [reuse_master_fields,reuse_master_fields]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
