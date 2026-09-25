import Proof.Packets.PacketsXLiteralAlphabet
import Proof.Packets.PacketsXNormalizedFolds

/-! Support and degree bounds at every accumulator boundary of the exact
ordered constructors. These bounds apply before source substitution as well
as to every partial product and partial parity sum during substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedIntermediate
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open LiteralAlphabet

def Bounded (S : Finset Nat) (d : Nat) (P : Ring.Poly Nat) : Prop :=
  Good S P ∧ Ring.Degree d P

theorem zero (S : Finset Nat) (d : Nat) : Bounded S d [] :=
  ⟨good_zero S,Normalized.degree_zero d⟩

theorem one (S : Finset Nat) (d : Nat) : Bounded S d [[]] := by
  refine ⟨⟨?_,?_⟩,Normalized.degree_one d⟩
  · simp [Ring.Normal]
  · intro m hm x hx
    simp only [List.mem_singleton] at hm
    subst m
    simp at hx

theorem mono {S : Finset Nat} {a b : Nat} {P : Ring.Poly Nat}
    (h : Bounded S a P) (hab : a≤b) : Bounded S b P :=
  ⟨h.1,Normalized.degree_mono h.2 hab⟩

theorem add {S : Finset Nat} {d : Nat} {P Q : Ring.Poly Nat}
    (hP : Bounded S d P) (hQ : Bounded S d Q) : Bounded S d (Ring.add P Q) := by
  exact ⟨good_add hP.1 hQ.1,Normalized.degree_add hP.2 hQ.2⟩

theorem mul {S : Finset Nat} {a b : Nat} {P Q : Ring.Poly Nat}
    (hP : Bounded S a P) (hQ : Bounded S b Q) : Bounded S (a+b) (Ring.mul P Q) :=
  ⟨good_mul hP.1 hQ.1,Ring.degree_mul hP.2 hQ.2⟩

theorem fold_add {S : Finset Nat} {d : Nat} (ps : List (Ring.Poly Nat))
    (hps : ∀ P∈ps,Bounded S d P) (A : Ring.Poly Nat) (hA : Bounded S d A) :
    Bounded S d (ps.foldl Ring.add A) := by
  induction ps generalizing A with
  | nil=>exact hA
  | cons P ps ih=>exact ih (fun Q hQ=>hps Q (by simp [hQ])) _ (add hA (hps P (by simp)))

theorem sum_prefix {S : Finset Nat} {d : Nat} (ps : List (Ring.Poly Nat))
    (hps : ∀ P∈ps,Bounded S d P) (n : Nat) :
    Bounded S d ((ps.take n).foldl Ring.add []) :=
  fold_add _ (fun P hP=>hps P (List.mem_of_mem_take hP)) _ (zero S d)

theorem fold_parity {S : Finset Nat} {d : Nat} (ps : List (Ring.Poly Nat))
    (hps : ∀ P∈ps,Bounded S d P) (A : Ring.Poly Nat) (hA : Bounded S d A) :
    Bounded S d (ps.foldl (fun acc P=>Ring.add P acc) A) := by
  induction ps generalizing A with
  | nil=>exact hA
  | cons P ps ih=>exact ih (fun Q hQ=>hps Q (by simp [hQ])) _ (add (hps P (by simp)) hA)

theorem parity_prefix {S : Finset Nat} {d : Nat} (ps : List (Ring.Poly Nat))
    (hps : ∀ P∈ps,Bounded S d P) (n : Nat) :
    Bounded S d ((ps.reverse.take n).foldl (fun acc P=>Ring.add P acc) []) :=
  fold_parity _ (fun P hP=>hps P (List.mem_reverse.mp (List.mem_of_mem_take hP))) _ (zero S d)

theorem product {S : Finset Nat} {a : Nat} (ps : List (Ring.Poly Nat))
    (hps : ∀ P∈ps,Bounded S a P) :
    Bounded S (a*ps.length) (Normalized.structuralGF2Product ps) := by
  induction ps with
  | nil=>exact one S _
  | cons P ps ih=>
    have h:=mul (hps P (by simp)) (ih (fun Q hQ=>hps Q (by simp [hQ])))
    simpa only [Normalized.structuralGF2Product,List.foldr_cons,List.length_cons,
      Nat.mul_add,Nat.mul_one,Nat.add_comm,Normalized.structuralGF2Mul] using h

theorem product_prefix {S : Finset Nat} {a : Nat} (ps : List (Ring.Poly Nat))
    (hps : ∀ P∈ps,Bounded S a P) (n : Nat) :
    Bounded S (a*ps.length)
      ((ps.reverse.take n).foldl (fun acc P=>Ring.mul P acc) [[]]) := by
  have h:=product ((ps.reverse.take n).reverse)
    (fun P hP=>hps P (List.mem_reverse.mp (List.mem_of_mem_take (List.mem_reverse.mp hP))))
  have he : Normalized.structuralGF2Product ((ps.reverse.take n).reverse)=
      (ps.reverse.take n).foldl (fun acc P=>Ring.mul P acc) [[]] := by
    rw [←NormalizedFolds.product_exact]
    simp only [NormalizedFolds.product,List.reverse_reverse,structuralGF2One]
  rw [he] at h
  apply mono h
  simp only [List.length_reverse,List.length_take]
  exact Nat.mul_le_mul_left a (Nat.min_le_right _ _)

theorem substituted_monomial {S : Finset Nat} {d : Nat}
    (atom : Nat→Ring.Poly Nat) (ha : ∀ code,Bounded S 1 (atom code))
    (m : List Nat) (hm : m.length≤d) :
    Bounded S d (NormalizedFolds.product (m.map atom)) := by
  rw [NormalizedFolds.product_exact]
  have h:=product (m.map atom) (fun P hP=>by obtain ⟨x,_,rfl⟩:=List.mem_map.mp hP;exact ha x)
  apply mono h
  simpa only [List.length_map,Nat.one_mul] using hm

theorem substitution_sum_prefix {S : Finset Nat} {d : Nat}
    (atom : Nat→Ring.Poly Nat) (ha : ∀ code,Bounded S 1 (atom code))
    (P : Ring.Poly Nat) (hP : Ring.Degree d P) (n : Nat) :
    Bounded S d ((P.reverse.take n).foldl
      (fun acc m=>Ring.add (NormalizedFolds.product (m.map atom)) acc) []) := by
  have h:=fold_parity ((P.reverse.take n).map (fun m=>NormalizedFolds.product (m.map atom)))
    (fun Q hQ=>by
      obtain ⟨m,hm,rfl⟩:=List.mem_map.mp hQ
      exact substituted_monomial atom ha m (hP m (List.mem_reverse.mp (List.mem_of_mem_take hm))))
    [] (zero S d)
  simpa only [List.foldl_map,Function.comp_def] using h

theorem census {S : Finset Nat} {d : Nat} {P : Ring.Poly Nat} (hP : Bounded S d P) :
    P.length≤(S.card+1)^d := Ring.size_bound S d hP.1.1 hP.2 hP.1.2

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedIntermediate
