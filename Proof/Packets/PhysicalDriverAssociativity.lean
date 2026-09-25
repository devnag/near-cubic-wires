import Proof.Packets.PhysicalAppendAssociativity

/-! Reassociate two equal population drivers and one depth driver when
switching from the 299-tape level loop to the embedded coordinate loop. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalDriverAssociativity

theorem reassociate {α : Type*} {t : Nat} (a : Fin t → α) (x z : α) :
    Fin.addCases (m:=t+2) (n:=1) (motive:=fun _=>α)
      (Fin.addCases (m:=t) (n:=2) (motive:=fun _=>α) a (fun _=>x)) (fun _=>z)=
    Fin.addCases (m:=t+1) (n:=2) (motive:=fun _=>α)
      (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>α) a (fun _=>x)) ![x,z] := by
  rw [←PhysicalAppendAssociativity.double a x]
  change Fin.append (Fin.append (Fin.append a (fun _ : Fin 1=>x)) (fun _ : Fin 1=>x)) (fun _ : Fin 1=>z)=_
  have tail : Fin.append (fun _ : Fin 1=>x) (fun _ : Fin 1=>z)=![x,z] := by
    funext i;fin_cases i <;>rfl
  rw [Fin.append_assoc,tail]
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalDriverAssociativity
