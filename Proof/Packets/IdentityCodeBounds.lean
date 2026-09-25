import Proof.Packets.IdentityCodeCache

/-! Explicit size and cost of the generated identity cache. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeLoop

theorem word_length (i : Nat) : (NativeLiteralCode.word i).length=i+6 := by
  simp [NativeLiteralCode.word,Nat.add_assoc]

theorem records_length_le (N : Nat) (xs : List Nat) (hxs : ∀i∈xs,i≤N) :
    (xs.flatMap NativeLiteralCode.word).length≤xs.length*(N+6) := by
  induction xs with
  | nil=>simp
  | cons i xs ih=>
    have hi:=hxs i (by simp)
    have ht:=ih (by intro j hj;exact hxs j (by simp [hj]))
    simp only [List.flatMap_cons,List.length_append,word_length,List.length_cons]
    nlinarith

theorem stream_length_le (N : Nat) : (stream N).length≤N*(N+6) := by
  have h:=records_length_le N ((List.range N).map (fun j=>N-1-j))
    (by intro i hi;obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi;omega)
  simpa [stream,List.flatMap_map] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeLoop
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeCache

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeCache
