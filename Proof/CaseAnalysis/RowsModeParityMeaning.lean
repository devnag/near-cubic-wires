import Proof.MachineModel.OrdinarySignedSortKey
import Mathlib.Data.Nat.Choose.Lucas

/-! Window coefficients need only binomial parity. Lucas's recurrence
reduces it to one implication test per pair of actual binary digits. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeParity
open SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def guard : List Bool→List Bool→Bool
  | [],[]=>true
  | a::as,b::bs=>(!b||a)&&guard as bs
  | _,_=>false

theorem choose_step (n k : Nat) :
    (n.choose k % 2 == 1)=((!(k%2==1)||(n%2==1))&&((n/2).choose (k/2)%2==1)) := by
  have h:=Choose.choose_modEq_choose_mod_mul_choose_div_nat (n:=n) (k:=k) (p:=2)
  change n.choose k%2=(n%2).choose (k%2)*(n/2).choose (k/2)%2 at h
  have hn : n%2=0 ∨ n%2=1:=by omega
  have hk : k%2=0 ∨ k%2=1:=by omega
  rcases hn with hn|hn <;> rcases hk with hk|hk
  all_goals simp [hn,hk] at h ⊢
  all_goals rw [h]

theorem guard_binary (w n k : Nat) (hn : n<2^w) (hk : k<2^w) :
    guard (binary w n) (binary w k)=(n.choose k%2==1) := by
  induction w generalizing n k with
  | zero =>
      have h0:n=0:=by simpa using hn
      have h1:k=0:=by simpa using hk
      subst n;subst k;rfl
  | succ w ih =>
      have hn' : n/2<2^w := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).2
        (by simpa [pow_succ] using hn)
      have hk' : k/2<2^w := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).2
        (by simpa [pow_succ] using hk)
      rw [binary,binary,guard,ih _ _ hn' hk']
      exact (choose_step n k).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsModeParity
