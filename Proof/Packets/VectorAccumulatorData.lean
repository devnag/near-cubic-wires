import Proof.Packets.PhysicalCopyInto
import Proof.Packets.ReusableNormalizedArithmeticLeft

/-! Resident accumulator storage alongside the reusable arithmetic arena.
Loading and saving are actual fixed-width copies with all heads restored. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads : Fin 36→Nat := Fin.addCases (m:=34) (n:=2) (motive:=fun _=>Nat) ReusableArithmetic.heads (fun _ : Fin 2=>0)
def tapes (B R : Nat) (left right stored : List (List Bool)) : Fin 36→List Bool :=
  Fin.addCases (m:=34) (n:=2) (motive:=fun _=>List Bool) (ReusableArithmetic.state B R left right)
    (![ZeroPadding.pad R stored.flatten,ZeroPadding.pad R (CompareMachine.word stored.length)] : Fin 2→List Bool)
def Fits (R : Nat) (P : List (List Bool)) := P.flatten.length≤R ∧ P.length+1≤R
def load := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 34 25)
  (PhysicalCopyInto.machine (31 : Fin 36) 35 28)
def save := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 25 34)
  (PhysicalCopyInto.machine (31 : Fin 36) 28 35)
def copyBudget (R : Nat) := 4*R+5

theorem flat_length (R : Nat) (P : List (List Bool)) (h : Fits R P) :
    (ZeroPadding.pad R P.flatten).length=R := by
  rw [ZeroPadding.pad_length,Nat.max_eq_left h.1]
theorem count_length (R : Nat) (P : List (List Bool)) (h : Fits R P) :
    (ZeroPadding.pad R (CompareMachine.word P.length)).length=R := by
  simp [CompareMachine.word,Nat.max_eq_left h.2]


theorem tapes_engine (B R : Nat) (left right stored : List (List Bool)) (i : Fin 34) :
    tapes B R left right stored (i.castAdd 2)=ReusableArithmetic.state B R left right i := by
  exact Fin.addCases_left i

theorem tapes_worker (B R : Nat) (left right stored : List (List Bool)) (i : Fin 30) :
    tapes B R left right stored ((i.castAdd 4).castAdd 2)=
      ZeroPadding.pad R (ReusableArithmetic.data B left right i) := by
  rw [tapes_engine]
  unfold ReusableArithmetic.state ReusableArithmetic.bank ReusableArithmetic.padded
  exact Fin.addCases_left i

theorem tapes_reserved (B R : Nat) (left right stored : List (List Bool)) (i : Fin 4) :
    tapes B R left right stored ((i.natAdd 30).castAdd 2)=
      (![List.replicate (R+3) false,UnaryTemplate.tape R,List.replicate R true,
        List.replicate (R+3) false] : Fin 4→List Bool) i := by
  rw [tapes_engine]
  unfold ReusableArithmetic.state ReusableArithmetic.bank
  exact Fin.addCases_right i

theorem tapes_stored (B R : Nat) (left right stored : List (List Bool)) (i : Fin 2) :
    tapes B R left right stored (i.natAdd 34)=
      (![ZeroPadding.pad R stored.flatten,ZeroPadding.pad R (CompareMachine.word stored.length)] : Fin 2→List Bool) i := by
  exact Fin.addCases_right i

theorem data_core (B : Nat) (left right : List (List Bool)) (i : Fin 24) :
    ReusableArithmetic.data B left right (i.castAdd 6)=NormalizeCold.data B [] i := by
  unfold ReusableArithmetic.data NormalizedMultiply.data
  exact Fin.addCases_left i

theorem data_extra (B : Nat) (left right : List (List Bool)) (i : Fin 6) :
    ReusableArithmetic.data B left right (i.natAdd 24)=NormalizedMultiply.extras B left right i := by
  unfold ReusableArithmetic.data NormalizedMultiply.data
  exact Fin.addCases_right i

theorem tapes_left_outside (B R : Nat) (left right selected stored : List (List Bool))
    (i : Fin 36) (h25 : i≠25) (h28 : i≠28) :
    tapes B R left right stored i=tapes B R selected right stored i := by
  revert h25 h28
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=30) (n:=4) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=24) (n:=6) (fun l=>?_) (fun l=>?_) k
      · intro _ _;rw [tapes_worker,tapes_worker,data_core,data_core]
      · intro hn25 hn28
        rw [tapes_worker,tapes_worker,data_extra,data_extra]
        fin_cases l
        · rfl
        · exact False.elim (hn25 rfl)
        · rfl
        · rfl
        · exact False.elim (hn28 rfl)
        · rfl
    · intro _ _;rw [tapes_reserved,tapes_reserved]
  · intro _ _;rw [tapes_stored,tapes_stored]

theorem tapes_right_outside (B R : Nat) (left right selected stored : List (List Bool))
    (i : Fin 36) (h26 : i≠26) (h27 : i≠27) :
    tapes B R left right stored i=tapes B R left selected stored i := by
  revert h26 h27
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=30) (n:=4) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=24) (n:=6) (fun l=>?_) (fun l=>?_) k
      · intro _ _;rw [tapes_worker,tapes_worker,data_core,data_core]
      · intro hn26 hn27
        rw [tapes_worker,tapes_worker,data_extra,data_extra]
        fin_cases l
        · rfl
        · rfl
        · exact False.elim (hn26 rfl)
        · exact False.elim (hn27 rfl)
        · rfl
        · rfl
    · intro _ _;rw [tapes_reserved,tapes_reserved]
  · intro _ _;rw [tapes_stored,tapes_stored]

theorem tapes_saved_outside (B R : Nat) (left right stored selected : List (List Bool))
    (i : Fin 36) (h34 : i≠34) (h35 : i≠35) :
    tapes B R left right stored i=tapes B R left right selected i := by
  revert h34 h35
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · intro _ _;rw [tapes_engine,tapes_engine]
  · intro h34 h35;fin_cases j
    · exact False.elim (h34 rfl)
    · exact False.elim (h35 rfl)

theorem update_pair_eq {t : Nat} (a b : Fin t→List Bool) (p q : Fin t) (x y : List Bool)
    (hpq : p≠q) (hp : b p=x) (hq : b q=y)
    (haway : ∀ i,i≠p→i≠q→a i=b i) :
    Function.update (Function.update a p x) q y=b := by
  funext i
  by_cases hiq : i=q
  · subst i;simp only [Function.update_self,hq]
  by_cases hip : i=p
  · subst i;simp only [Function.update_of_ne hpq,Function.update_self,hp]
  simp only [Function.update_of_ne hiq,Function.update_of_ne hip]
  exact haway i hip hiq

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
