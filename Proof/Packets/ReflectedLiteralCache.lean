import Proof.MachineModel.Encoding
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-! Literal cache order for the actual descending index driver. These are
native singleton polynomial words; no completed support bank is assumed. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReflectedLiteralCache
open NearCubicWires

def codes (tag count : Nat) := List.ofFn (fun i : Fin count=>Nat.pair tag i.val)
def descending (tag count : Nat) := (List.range count).map (fun i=>Nat.pair tag (count-1-i))
def singletonWord (code : Nat) := ExtIncidence.stream [[code]] ++ ExtIncidence.stream []
def stream (tag count : Nat) := (descending tag count).flatMap singletonWord

theorem descending_eq (tag count : Nat) : descending tag count=(codes tag count).reverse := by
  apply List.ext_getElem
  · simp [descending,codes]
  · intro i h₁ h₂
    simp only [descending,codes,List.getElem_map,List.getElem_range,List.getElem_reverse,
      List.length_ofFn,List.getElem_ofFn]

theorem singletonWord_eq (code : Nat) : singletonWord code=
    true::(List.replicate (code+1) true++[false,false,false,false]) := by
  simp [singletonWord,ExtIncidence.stream,ExtIncidence.monomialWord,ExtIncidence.block,List.append_assoc]

theorem singletonWord_length (code : Nat) : (singletonWord code).length=code+6 := by
  rw [singletonWord_eq]
  simp

theorem stream_eq (tag count : Nat) : stream tag count=
    ((codes tag count).reverse.map (fun c=>([[c]],([] : List (List Nat))))).flatMap
      (fun p=>ExtIncidence.stream p.1++ExtIncidence.stream p.2) := by
  simp only [stream,descending_eq,List.flatMap_map]
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.ReflectedLiteralCache
