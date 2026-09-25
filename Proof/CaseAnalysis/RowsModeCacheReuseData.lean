import Proof.CaseAnalysis.RowsModeCacheReuseClear

/-! The enclosing return uses field identities before substituting the
large actual population state into the fixed tape layout. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reuseLift (R D : Nat) (A : Fin 25→List Bool) : Fin 28→List Bool:=
  Fin.addCases (m:=26) (n:=2) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=25) (n:=1) (motive:=fun _=>List Bool) A (fun _=>List.replicate R false))
    (![List.replicate D true,List.replicate (D+1) false])

theorem reuse_lift (p : Parameters) (M R D : Nat) (out : List Bool) (A : Fin 15→List Bool)
    (X : Fin 25→List Bool) (hx : ∀ i,X i=reuseData p M R D out A (i.castAdd 3)) :
    reuseLift R D X=reuseData p M R D out A:=by
  funext i
  refine Fin.addCases (m:=26) (n:=2) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=25) (n:=1) (fun k=>?_) (fun k=>?_) j
    · simp only [reuseLift,Fin.addCases_left]
      exact hx k
    · fin_cases k;rfl
  · fin_cases j <;> rfl

theorem reuse_initial_old (p : Parameters) (M R D : Nat) (out : List Bool)
    (hD : p.C+1 ≤ D) (hr : p.rank+1 ≤ D) (hd : 3 ≤ D) (i : Fin 25) :
    ZeroPadding.pad (reuseCaps D i) (initData p M out 0 i)=
      reuseData p M R D out (fun _=>List.replicate D false) (i.castAdd 3):=by
  have log (A : Fin 15→List Bool) : reuseData p M R D out A=
      Function.update (reuseData p M 0 D out A) 25 (List.replicate R false):=by
    funext j;fin_cases j <;> rfl
  rw [log,Function.update_of_ne (show i.castAdd 3≠25 by intro he;have hh:=congrArg Fin.val he;have hi:=i.isLt;change i.val=25 at hh;omega)]
  exact congrFun (reuse_initial p M D out hD hr hd) i

def reusePrivate (p : Parameters) (s : State) : Fin 15→List Bool:=
  ![label p s,List.replicate p.C false,List.replicate p.C false,List.replicate p.C false,
    List.replicate p.C false,List.replicate p.C false,[s.zero],[s.sibling],[s.child],[s.var],[s.neg],
    UnaryTemplate.tape (s.index+1),RepairSource.VerifierDecoding.CompareMachine.word s.selectedCount,
    List.replicate (p.C+1) false,RepairSource.VerifierDecoding.CompareMachine.word s.children]
theorem reuse_private_fields (p : Parameters) (M : Nat) (s : State) (j : Fin 15) :
    loopData p s M (privateSlots j)=reusePrivate p s j:=by
  fin_cases j <;> rfl

theorem reuse_padded_old (p : Parameters) (M R D : Nat) (s : State) (i : Fin 25) :
    ZeroPadding.pad (reuseCaps D i) (loopData p s M i)=
      reuseData p M R D s.out (fun j=>ZeroPadding.pad D (reusePrivate p s j)) (i.castAdd 3):=by
  fin_cases i <;>
    simp [reuseCaps,loopData,data,fields,CloseoutRowsModeHashFields.before,extras,reuseData,
      reusePrivate,Fin.addCases,ZeroPadding.pad_zero]

theorem reuse_final_old (p : Parameters) (M R D : Nat) (s : State) (out : List Bool) (i : Fin 25) :
    ZeroPadding.pad (reuseCaps D i) (loopData p {s with out:=out} M i)=
      reuseData p M R D out
        (fun j=>ZeroPadding.pad D (loopData p {s with out:=[]} M (privateSlots j))) (i.castAdd 3):=by
  simp_rw [reuse_private_fields]
  exact reuse_padded_old p M R D {s with out:=out} i

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
