import Proof.Packets.PacketsXDescendingWindowLoop
import Proof.Packets.PacketsXWindowNativeOrder

/-! Literal native bytes emitted by the two actual descending loops. The
empty-population branch emits the correct constant monomial too. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowMeaning
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RowTupleSubsets
open CloseoutRowsModeWindowBinomial CloseoutRowsModeWindowScalar

def summand (v M a : Nat) (guard : Bool) : Ring.Poly Nat := if guard then selected v M a else []

theorem selected_empty (v a : Nat) : selected v 0 a=if a=0 then [[]] else [] := by
  have h:=selected_perm v 0 a (Nat.zero_le _)
  cases a <;> simpa using h

theorem word_summand (v M a : Nat) (guard : Bool) :
    CloseoutRowsModeWindowEmit.word v a M guard=(summand v M a guard).flatMap ExtIncidence.monomialWord := by
  cases guard
  · rfl
  · by_cases hM:M=0
    · subst M
      rw [summand,if_pos rfl,selected_empty]
      cases a <;> simp [CloseoutRowsModeWindowEmit.word,ExtIncidence.monomialWord]
    · simp [CloseoutRowsModeWindowEmit.word,summand,hM,CloseoutRowsModeElementary.bodyWord,
        CloseoutRowsModeElementary.monomials]

theorem guarded_scales (n m : Nat) (P : Ring.Poly Nat) :
    (if (n%2==1)&&(m%2==1) then P else [])=gf2ParityScale n (gf2ParityScale m P) := by
  have hn:=Nat.mod_lt n (by decide : 0<2)
  have hm:=Nat.mod_lt m (by decide : 0<2)
  have en:n%2=0∨n%2=1:=by omega
  have em:m%2=0∨m%2=1:=by omega
  rcases en with en|en <;> rcases em with em|em <;> simp [gf2ParityScale,en,em]

theorem scale_flatMap (n : Nat) (xs : List Nat) (f : Nat→Ring.Poly Nat) :
    gf2ParityScale n (xs.flatMap f)=xs.flatMap (fun x=>gf2ParityScale n (f x)) := by
  unfold gf2ParityScale
  by_cases h:n%2=0 <;> simp [h]

theorem block_word (v M offset target d : Nat) :
    DescendingWindowLoop.block v M offset target d=
      (gf2ParityScale (d.choose target) (WindowNativeOrder.positionalShifted v M offset d)).flatMap
        ExtIncidence.monomialWord := by
  unfold DescendingWindowLoop.block WindowNativeOrder.positionalShifted
  rw [scale_flatMap,List.flatMap_assoc]
  apply List.flatMap_congr
  intro j _
  rw [DescendingWindow.emit,word_summand]
  apply congrArg (List.flatMap ExtIncidence.monomialWord)
  exact guarded_scales _ _ _

theorem output_word (v M offset target width : Nat) (out : List Bool) :
    DescendingWindowLoop.output v M offset target out (width+1)=
      out++(WindowNativeOrder.positionalWindow v M offset width target).flatMap ExtIncidence.monomialWord := by
  unfold DescendingWindowLoop.output WindowNativeOrder.positionalWindow
  rw [List.flatMap_assoc]
  apply congrArg (List.append out)
  apply List.flatMap_congr
  intro d _
  exact block_word v M offset target d

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowMeaning
