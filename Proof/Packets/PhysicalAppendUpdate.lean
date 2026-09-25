import Proof.Rows.PhysicalFocusBoundary

/-! Canonical equality for updating an existing tape through a fixed append. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalAppendUpdate

theorem left {α : Sort*} {t e : Nat} (a : Fin t→α) (extra : Fin e→α) (port : Fin t) (value : α) :
    Function.update (Fin.addCases (m:=t) (n:=e) (motive:=fun _=>α) a extra) (port.castAdd e) value=
      Fin.addCases (m:=t) (n:=e) (motive:=fun _=>α) (Function.update a port value) extra := by
  funext i
  refine Fin.addCases (m:=t) (n:=e) (fun j=>?_) (fun j=>?_) i
  · by_cases he:j=port
    · subst j;rw [Function.update_self,Fin.addCases_left,Function.update_self]
    · have hn:j.castAdd e≠port.castAdd e := by intro h;exact he (Fin.ext (congrArg (fun z : Fin (t+e)=>z.val) h))
      rw [Function.update_of_ne hn,Fin.addCases_left,Fin.addCases_left,Function.update_of_ne he]
  · have hn:j.natAdd t≠port.castAdd e := by
      intro h;have hv:=congrArg Fin.val h;dsimp at hv;have hp:=port.isLt;omega
    rw [Function.update_of_ne hn,Fin.addCases_right,Fin.addCases_right]

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalAppendUpdate
