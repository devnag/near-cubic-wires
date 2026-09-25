import Proof.Packets.PacketsXNormalizedRing

/-! Forward physical traversals for the fixed constructors' exact fold order.
Every right fold reads a reversed resident bank and puts the newly read operand
on the left. No algebraic commutativity or associativity is used. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedFolds
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram

def product (polynomials : List StructuralGF2Polynomial) : StructuralGF2Polynomial :=
  polynomials.reverse.foldl (fun accumulator polynomial=>Ring.mul polynomial accumulator) structuralGF2One

def substitute (atom : Nat → StructuralGF2Polynomial)
    (polynomial : StructuralGF2Polynomial) : StructuralGF2Polynomial :=
  polynomial.reverse.foldl (fun accumulator monomial=>Ring.add (product (monomial.map atom)) accumulator) []

theorem product_exact (polynomials : List StructuralGF2Polynomial) :
    product polynomials=Normalized.structuralGF2Product polynomials := by
  change polynomials.reverse.foldl (fun acc p=>Ring.mul p acc) structuralGF2One=
    polynomials.foldr Ring.mul structuralGF2One
  exact List.foldl_reverse

theorem finiteParity_foldr {arity : Nat} (polynomials : Fin arity → StructuralGF2Polynomial) :
    Normalized.structuralGF2FinParity polynomials=(List.ofFn polynomials).foldr Ring.add [] := by
  induction arity with
  | zero=>rfl
  | succ arity ih=>
    simp only [Normalized.structuralGF2FinParity,List.ofFn_succ,List.foldr_cons,
      Normalized.structuralGF2Add,ih]

theorem substitute_foldr (atom : Nat → StructuralGF2Polynomial)
    (polynomial : StructuralGF2Polynomial) :
    Normalized.structuralGF2Substitute atom polynomial=
      polynomial.foldr (fun monomial accumulator=>Ring.add (product (monomial.map atom)) accumulator) [] := by
  induction polynomial with
  | nil=>rfl
  | cons monomial polynomial ih=>
    simp only [Normalized.structuralGF2Substitute,List.foldr_cons,
      Normalized.structuralGF2Add,ih,product_exact]

theorem substitute_exact (atom : Nat → StructuralGF2Polynomial)
    (polynomial : StructuralGF2Polynomial) :
    substitute atom polynomial=Normalized.structuralGF2Substitute atom polynomial := by
  rw [substitute_foldr]
  simp only [substitute,List.foldl_reverse]

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedFolds
