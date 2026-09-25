import Proof.Packets.PacketsXComplementPacketBank
import Proof.Packets.PacketsXSelectedPairFetch

/-! Exact list-level meaning of the physically paired majority factor bank. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PairedPacketMeaning
open NormalizedFiniteTransport ComplementPacketBank
abbrev Poly:=Ring.Poly Nat

def literal (P : Poly) (b : Bool) : Poly:=if b then P else Ring.add [[]] P

theorem pairs_length (ps : List Poly) : (pairs ps).length=2*ps.length := by
  induction ps with
  | nil=>rfl
  | cons P ps ih=>simp [pairs] at ih ⊢;omega

theorem pair_get (ps : List Poly) (i : Nat) (b : Bool) (hi : i<ps.length) :
    (pairs ps).getD (SelectedPairFetch.chosen i b) []=literal ps[i] b := by
  induction ps generalizing i with
  | nil=>simp at hi
  | cons P ps ih=>
    cases i with
    | zero=>cases b <;>rfl
    | succ i=>
      have hi' : i<ps.length:=by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      have h:=ih i hi'
      cases b <;>simpa [pairs,SelectedPairFetch.chosen,literal,Nat.mul_add,Nat.add_assoc,
        List.getD_cons_succ] using h

def factors (ps : List Poly) (bits : List Bool) : List Poly:=
  List.ofFn (fun i : Fin ps.length=>literal ps[i.val] (bits.getD i.val false))

theorem factors_length (ps : List Poly) (bits : List Bool) : (factors ps bits).length=ps.length:=by
  simp [factors]

theorem factors_get (ps : List Poly) (bits : List Bool) (i : Nat) (hi : i<ps.length) :
    (factors ps bits).getD i []=literal ps[i] (bits.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simpa [factors] using hi)]
  simp [factors]

theorem factor_bounded (S : Finset Nat) (d : Nat) (P : Poly) (b : Bool)
    (hP : NormalizedIntermediate.Bounded S d P) : NormalizedIntermediate.Bounded S d (literal P b) := by
  cases b
  · exact NormalizedIntermediate.add (NormalizedIntermediate.one S d) hP
  · exact hP

theorem pairs_bounded (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P) :
    ∀P∈pairs ps,NormalizedIntermediate.Bounded S d P := by
  intro P hP
  obtain ⟨Q,hQ,hP⟩:=List.mem_flatMap.mp hP
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hP
  rcases hP with rfl|rfl
  · exact hps _ hQ
  · exact NormalizedIntermediate.add (NormalizedIntermediate.one S d) (hps Q hQ)

theorem factors_bounded (S : Finset Nat) (d : Nat) (ps : List Poly) (bits : List Bool)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P) :
    ∀P∈factors ps bits,NormalizedIntermediate.Bounded S d P := by
  intro P hP
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hP
  exact factor_bounded S d _ _ (hps _ (List.getElem_mem i.isLt))

end PCJ9eff70d512234a4c_Fixed.Materializer.PairedPacketMeaning
