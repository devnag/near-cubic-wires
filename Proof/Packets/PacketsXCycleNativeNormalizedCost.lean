import Proof.Packets.NativeNormalized
import Proof.Packets.PacketsXCycleArithmeticCost

/-! The actual native parser, counted rewind and normalization fit the same
common reserve, including raw window sources with up to 2^(2w) monomials. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.RepairOrdinary
open PCJ9eff70d512234a4c_Fixed.Materializer

 theorem sum_map_bound {α : Type} (xs : List α) (f : α→Nat) (B : Nat)
    (h : ∀ x∈xs,f x≤B) : (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

 theorem native_monomial_cost (C : Nat) (m : List Nat)
    (hc : ∀ code∈m,code<C) (hm : m.length≤C) :
    ExtIncidence.monomialCost C m≤4*(C+1)^2 := by
  have hs:=sum_map_bound m ExtIncidence.blockCost (2*C+4)
    (fun code hcode=>by have h:=hc code hcode;unfold ExtIncidence.blockCost;omega)
  have hm':=Nat.mul_le_mul_right (2*C+4) hm
  unfold ExtIncidence.monomialCost
  nlinarith

 theorem native_parser_cost (C : Nat) (P : List (List Nat))
    (hc : ∀ m∈P,∀ code∈m,code<C) (hd : ∀ m∈P,m.length≤C) :
    ExtIncidence.cost C P≤4*P.length*(C+1)^2+1 := by
  have h:=sum_map_bound P (ExtIncidence.monomialCost C) (4*(C+1)^2)
    (fun m hm=>native_monomial_cost C m (hc m hm) (hd m hm))
  unfold ExtIncidence.cost
  nlinarith

 theorem native_budget_polynomial (C : Nat) (P : List (List Nat))
    (hc : ∀ m∈P,∀ code∈m,code<C) (hd : ∀ m∈P,m.length≤C) :
    NativeNormalized.budget C P+3≤8192*(P.length+1)^3*(C+1)^3 := by
  have hp:=native_parser_cost C P hc hd
  have ha:=addition_ready_polynomial C 0 P.length
  simp only [Nat.zero_mul,Nat.zero_add] at ha
  have hn:=normalizer_budget_polynomial C (NativeNormalized.masks C P)
    (NativeNormalized.masks_width C P)
  simp only [NativeNormalized.masks,List.length_map] at hn
  have prep : NativeNormalized.prepareBudget C P+MaskAddition.budget C 0 P.length+5≤
      256*(P.length+1)*(C+1)^2 := by
    unfold NativeNormalized.prepareBudget
    nlinarith only [hp,ha,Nat.zero_le (P.length*C^2),Nat.zero_le (C^2),
      Nat.zero_le (P.length*C),Nat.zero_le P.length,Nat.zero_le C]
  have hpoly : (P.length+1)*(C+1)^2≤(P.length+1)^3*(C+1)^3 :=
    Nat.mul_le_mul (Nat.le_self_pow (by decide) _) (Nat.pow_le_pow_right (by omega) (by omega))
  have hpre:=Nat.mul_le_mul_left 256 hpoly
  unfold NativeNormalized.budget NormalizedAddition.budget
  simp only [NativeNormalized.masks,List.length_map,List.length_nil,List.reverse_nil,List.nil_append]
  nlinarith only [prep,hpre,hn,Nat.zero_le ((P.length+1)^3*(C+1)^3)]

 theorem native_budget_reserve (C w : Nat) (P : List (List Nat))
    (hc : ∀ m∈P,∀ code∈m,code<C) (hd : ∀ m∈P,m.length≤C) (hcount : P.length≤2^(2*w)) :
    NativeNormalized.budget C P+3≤commonReserve C w :=
  (native_budget_polynomial C P hc hd).trans (packet_reserve_bound C w P.length hcount)

 theorem native_monomial_length (C : Nat) (m : List Nat) :
    (ExtIncidence.monomialWord m).length≤ExtIncidence.monomialCost C m := by
  have hb : (m.flatMap ExtIncidence.block).length≤(m.map ExtIncidence.blockCost).sum := by
    induction m with
    | nil=>simp
    | cons x xs ih=>
      simp only [List.flatMap_cons,List.length_append,ExtIncidence.block_length,List.map_cons,List.sum_cons]
      simp only [ExtIncidence.blockCost] at ih ⊢
      omega
  rw [ExtIncidence.monomialWord_length]
  unfold ExtIncidence.monomialCost
  omega

 theorem native_stream_length (C : Nat) (P : List (List Nat)) :
    (ExtIncidence.stream P).length≤ExtIncidence.cost C P := by
  induction P with
  | nil=>simp [ExtIncidence.stream,ExtIncidence.cost]
  | cons m ms ih=>
    rw [ExtIncidence.stream_cons,List.length_append,ExtIncidence.cost_cons]
    exact Nat.add_le_add (native_monomial_length C m) ih

 theorem native_input_reserve (C w : Nat) (P : List (List Nat))
    (hc : ∀ m∈P,∀ code∈m,code<C) (hd : ∀ m∈P,m.length≤C) (hcount : P.length≤2^(2*w)) :
    ∀ i,(NativeNormalized.A C P [] i).length≤commonReserve C w := by
  have hb:=native_budget_reserve C w P hc hd hcount
  have ha:=arithmetic_input_reserve C w [] [] (by simp) (by simp) (by simp) (by simp)
  have he : NormalizedAddition.data C [] [] []=NormalizedMultiply.data C [] [] [] := by
    funext j;fin_cases j <;>rfl
  intro i
  refine Fin.addCases (m:=30) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [NativeNormalized.A,Fin.addCases_left,he]
    exact ha j
  · fin_cases j
    · change (ExtIncidence.stream P).length≤_
      apply (native_stream_length C P).trans
      apply le_trans (b:=NativeNormalized.budget C P+3) ?_ hb
      unfold NativeNormalized.budget NativeNormalized.prepareBudget
      omega
    · rw [NativeNormalized.A,Fin.addCases_right]
      change (List.replicate C false).length≤_
      rw [List.length_replicate]
      have h:=ha 24
      change (UnaryTemplate.tape C).length≤commonReserve C w at h
      simp only [UnaryTemplate.tape,List.length_cons,List.length_append,List.length_replicate] at h
      omega

end Theorem25Completion.CycleBounds
