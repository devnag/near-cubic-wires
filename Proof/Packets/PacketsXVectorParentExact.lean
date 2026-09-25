import Proof.Packets.PacketsXVectorWorkerParentLoop
import Proof.Packets.NormalizedVector

/-! The stored parent answers have precisely the frozen level-vector order. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule

variable {rank depth population : Nat}

def levelDelta (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth→Nat) (level : Fin depth) (parent child : Nat) : Ring.Poly Nat :=
  if hp:parent<population+1 then
    if hc:child<population+1 then Normalized.structuralDeltaFactor label seed window level ⟨parent,hp⟩ ⟨child,hc⟩
    else []
  else []

theorem parent_level_exact (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth→Nat) (level : Fin depth) (previous : List (Ring.Poly Nat))
    (hlen : previous.length=population+1) :
    List.ofFn (fun j : Fin previous.length=>parentAnswer previous (levelDelta label seed window level) j.val)=
      NormalizedVector.level label seed window level previous := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,NormalizedVector.level_length,hlen]
  · intro parent hleft hright
    have hp:parent<population+1 := by simpa only [NormalizedVector.level_length] using hright
    simp only [List.getElem_ofFn,NormalizedVector.level,parentAnswer,VectorParentPrefix.finish]
    apply congrArg Normalized.structuralGF2Sum
    apply List.ext_getElem
    · rw [VectorParentPrefix.terms_length,List.length_ofFn,hlen]
    · intro child hc1 hc2
      have hc:child<population+1 := by simpa only [List.length_ofFn] using hc2
      have hcp:child<previous.length := by omega
      simp only [VectorParentPrefix.terms,List.getElem_ofFn,levelDelta,dif_pos hp,dif_pos hc]
      simp only [List.getD,List.getElem?_eq_getElem hcp,Option.getD_some]
      rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
