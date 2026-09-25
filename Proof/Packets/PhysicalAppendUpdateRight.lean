import Proof.Packets.PhysicalAppendUpdate

/-! Updating a tape in the right block of a fixed tape embedding. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalAppendUpdate

theorem right {α : Sort*} {t e : Nat} (a : Fin t→α) (extra : Fin e→α) (port : Fin e) (value : α) :
    Function.update (Fin.addCases (m:=t) (n:=e) (motive:=fun _=>α) a extra) (port.natAdd t) value=
      Fin.addCases (m:=t) (n:=e) (motive:=fun _=>α) a (Function.update extra port value) := by
  funext i
  refine Fin.addCases (m:=t) (n:=e) (fun j=>?_) (fun j=>?_) i
  · have hn:j.castAdd e≠port.natAdd t := by
      intro h
      have hv:=congrArg (fun z : Fin (t+e)=>z.val) h
      dsimp at hv
      have hj:=j.isLt
      omega
    rw [Function.update_of_ne hn,Fin.addCases_left,Fin.addCases_left]
  · by_cases he:j=port
    · subst j;rw [Function.update_self,Fin.addCases_right,Function.update_self]
    · have hn:j.natAdd t≠port.natAdd t := by
        intro h
        apply he
        apply Fin.ext
        have hv:=congrArg (fun z : Fin (t+e)=>z.val) h
        dsimp at hv
        omega
      rw [Function.update_of_ne hn,Fin.addCases_right,Fin.addCases_right,Function.update_of_ne he]

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalAppendUpdate
