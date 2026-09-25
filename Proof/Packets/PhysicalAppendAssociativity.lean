import Proof.Rows.PhysicalFocusBoundary

/-! Two equal appended driver words have the same canonical array as one
two-word append. This only aligns physical configurations, not tape contents. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalAppendAssociativity

theorem double {α : Sort*} {t : Nat} (a : Fin t→α) (e : α) :
    Fin.addCases (m:=t+1) (n:=1) (motive:=fun _=>α)
      (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>α) a (fun _=>e)) (fun _=>e)=
    Fin.addCases (m:=t) (n:=2) (motive:=fun _=>α) a (fun _=>e) := by
  funext i
  refine Fin.addCases (m:=t) (n:=2) (fun j=>?_) (fun j=>?_) i
  · have he : j.castAdd 2=(j.castAdd 1).castAdd 1:=rfl
    rw [he,Fin.addCases_left,Fin.addCases_left,show (j.castAdd 1).castAdd 1=j.castAdd 2 from rfl,Fin.addCases_left]
  · fin_cases j
    · rw [Fin.addCases_right]
      change (Fin.addCases (m:=t+1) (n:=1) (motive:=fun _=>α)
        (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>α) a (fun _=>e)) (fun _=>e))
          (((0 : Fin 1).natAdd t).castAdd 1)=e
      rw [Fin.addCases_left,Fin.addCases_right]
    · rw [Fin.addCases_right]
      change (Fin.addCases (m:=t+1) (n:=1) (motive:=fun _=>α)
        (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>α) a (fun _=>e)) (fun _=>e))
          ((0 : Fin 1).natAdd (t+1))=e
      rw [Fin.addCases_right]

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalAppendAssociativity
