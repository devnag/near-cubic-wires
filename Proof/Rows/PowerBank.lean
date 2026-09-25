import Proof.Rows.ScalarReplace

/-! The coefficient mapper's actual bank with a retained full-width base and
one isolated product destination. The growing coefficient output stays at64. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_PowerBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_ResidueScaleCell.palette

def factorCap (U : Nat) (i : Fin 91) := if i=28 then U else 0
def base (a p w F U : Nat) (source out coefficient : List Bool) (i : Fin 91) :=
  ZeroPadding.pad (factorCap U i) (PCJ45bee56da9f34d5a_NativeScaleInput.bank a p w F U source out coefficient i)
def bank (a B p w F U q : Nat) (source out coefficient temp : List Bool) : Fin 94→List Bool :=
  Fin.addCases (m:=91) (n:=3) (motive:=fun _=>List Bool) (base a p w F U source out coefficient)
    ![CompareMachine.word q,ZeroPadding.pad U (frame (binary w B)),ZeroPadding.pad U temp]
def heads (pos len tpos : Nat) : Fin 94→Nat :=
  Fin.addCases (m:=91) (n:=3) (motive:=fun _=>Nat) (PCJ45bee56da9f34d5a_NativeScaleInput.heads pos len 0) ![1,0,tpos]

def productSlots (i : Fin 65) : Fin 94 := if i=64 then 93 else ⟨i.val,by omega⟩
theorem product_injective : Function.Injective productSlots := by decide
def productCaps (U : Nat) (i : Fin 65) := if i=0 ∨ i=28 ∨ i=64 then U else 0

theorem main_out_eq (a p w U : Nat) (out temp coefficient : List Bool) (i : Fin 65) (hi : i≠64) :
    PCJ45bee56da9f34d5a_NativeScaleInput.main a p w U out coefficient i =
      PCJ45bee56da9f34d5a_NativeScaleInput.main a p w U temp coefficient i := by
  unfold PCJ45bee56da9f34d5a_NativeScaleInput.main
  split_ifs
  · rfl
  · have hv : i.val≠64 := fun h=>hi (Fin.ext h)
    let j : Fin 64:=⟨i.val,by have h:=i.isLt;omega⟩
    have he : i=j.castAdd 1:=Fin.ext rfl
    rw [he]
    simp only [PCJ45bee56da9f34d5a_ResidueScaleCell.cold,Fin.addCases_left]

theorem product_bank (a b B p w F U q : Nat) (source out temp : List Bool) (i : Fin 65) :
    bank a B p w F U q source out (ZeroPadding.pad U (frame (binary w b))) temp (productSlots i) =
      ZeroPadding.pad (productCaps U i) (PCJ45bee56da9f34d5a_ResidueScaleCell.cold
        (PCJ45bee56da9f34d5a_ResidueScaleCell.palette a b p w) U temp i) := by
  by_cases hi:i=64
  · subst i;rfl
  · have he : productSlots i=(i.castAdd 26).castAdd 3 := by
      apply Fin.ext;simp [productSlots,hi]
    rw [he]
    simp only [bank,Fin.addCases_left,base,PCJ45bee56da9f34d5a_NativeScaleInput.bank]
    rw [main_out_eq a p w U out temp _ i hi]
    rw [←congrFun (PCJ45bee56da9f34d5a_NativeScaleInput.main_eq a b p w U temp) i]
    by_cases h28:i=28
    · subst i;simp [factorCap,productCaps,ZeroPadding.pad_zero]
    · have hc : i.castAdd 26≠(28 : Fin 91) := fun h=>h28 (Fin.ext (congrArg (fun j : Fin 91=>j.val) h))
      simp only [factorCap,if_neg hc,ZeroPadding.pad_zero,productCaps,h28,hi,or_false]

theorem product_head (pos : Nat) (out temp : List Bool) (i : Fin 65) :
    heads pos out.length temp.length (productSlots i)=PCJ45bee56da9f34d5a_ResidueScaleCell.heads temp 0 i := by
  fin_cases i <;>rfl

theorem bank_away (a B p w F U q : Nat) (source out coefficient coefficient' temp temp' : List Bool)
    (i : Fin 94) (hi : i≠0) (ht : i≠93) :
    bank a B p w F U q source out coefficient temp i=bank a B p w F U q source out coefficient' temp' i := by
  fin_cases i <;>first |rfl |contradiction

end
end PCJ45bee56da9f34d5a_PowerBank
