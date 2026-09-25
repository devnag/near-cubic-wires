import Proof.Assembly.RowProduction
import Proof.Rows.RowsModeThresholdScalars

/-! Exact consumer identity for the streamed canonical mixed-radix equation.
Each selected child contributes its scaled weights and its own negative target.
The final offset is a single further constant summand. Empty supports and empty
circuit lists use the same construction. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ExpandedThresholdStream
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.ThresholdCompiler
open PCJ9eff70d512234a4c_Fixed
open scoped BigOperators
noncomputable section

def mass (xs : List (Int×Bool)) : Int:=
  (xs.map (fun x=>x.1*(x.2.toNat : Int))).sum

def block {n : Nat} (g : ExactThresholdGate n) (bits : Fin n→Bool) (factor : Int) : List (Int×Bool):=
  List.ofFn (fun j=>(factor*g.weight j,bits j))++[(-(factor*g.target),true)]

theorem mass_append (xs ys : List (Int×Bool)) : mass (xs++ys)=mass xs+mass ys:=by
  simp [mass,List.map_append,List.sum_append]

theorem mass_block {n : Nat} (g : ExactThresholdGate n) (bits : Fin n→Bool) (factor : Int) :
    mass (block g bits factor)=factor*((∑ j,g.weight j*(bits j).toNat)-g.target):=by
  simp only [mass,block,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,
    List.sum_append,List.sum_ofFn,List.sum_cons,List.sum_nil,Bool.toNat_true,
    Nat.cast_one,mul_one,add_zero,Function.comp_apply]
  simp only [mul_assoc,←Finset.mul_sum]
  ring

theorem mass_flatMap {α : Type} (xs : List α) (f : α→List (Int×Bool)) :
    mass (xs.flatMap f)=(xs.map (fun x=>mass (f x))).sum:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.flatMap_cons,mass_append,List.map_cons,List.sum_cons,ih]

theorem stack_difference {Carrier : Type} [Fintype Carrier] (base : Int) {n : Nat}
    (es : Fin n→LabelledEquation Carrier) (bits : Carrier→Bool) :
    (stackEquations base (List.ofFn es)).difference bits=
      ∑ i : Fin n,base^i.val*(es i).difference bits:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    rw [List.ofFn_succ,stackEquations_difference_cons,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,pow_zero,one_mul,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_succ,pow_succ]
    ring

variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (sel : ThresholdRows.Selection a r)

def terms (bits : Fin (thresholdFourfoldOccurrences r).length→Bool) : List (Int×Bool):=
  (List.ofFn (fun i : Fin r.circuits.length=>i)).flatMap (fun i=>
    block ((ThresholdRows.children a (r.circuits.get i)).get (sel i))
      (fun j=>bits (thresholdCircuitEmbedding r i j))
      (equationListBase (ThresholdRows.equations a r sel)^i.val))

theorem mass_terms (bits : Fin (thresholdFourfoldOccurrences r).length→Bool) :
    mass (terms a r sel bits)=(ThresholdRows.equation a r sel).difference bits:=by
  unfold ThresholdRows.equation canonicalEquationStack ThresholdRows.equations
  rw [stack_difference]
  change mass ((List.ofFn (fun i : Fin r.circuits.length=>i)).flatMap
    (fun i=>block ((ThresholdRows.children a (r.circuits.get i)).get (sel i))
      (fun j=>bits (thresholdCircuitEmbedding r i j))
      (equationListBase (ThresholdRows.equations a r sel)^i.val)))=_
  rw [mass_flatMap,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [Function.comp_apply]
  rw [mass_block]
  unfold LabelledEquation.difference LabelledEquation.score thresholdChildEquation
  simp only [embeddedWeight_score,bitInt_eq_toNat]
  rfl

def equation (bits : Fin (thresholdFourfoldOccurrences r).length→Bool) (offset : Nat) :
    LabelledEquation (Fin (terms a r sel bits).length):=
  {weights:=fun i=>((terms a r sel bits).get i).1,target:=(offset : Int)}
def input (bits : Fin (thresholdFourfoldOccurrences r).length→Bool) :
    Fin (terms a r sel bits).length→Bool:=fun i=>((terms a r sel bits).get i).2

theorem expanded_difference (bits : Fin (thresholdFourfoldOccurrences r).length→Bool) (offset : Nat) :
    (equation a r sel bits offset).difference (input a r sel bits)=
      (ThresholdRows.equation a r sel).difference bits-(offset : Int):=by
  rw [←mass_terms a r sel bits]
  unfold equation input LabelledEquation.difference LabelledEquation.score
  congr 1
  have h : List.ofFn (fun i : Fin (terms a r sel bits).length=>(terms a r sel bits).get i)=terms a r sel bits:=by
    simpa only [List.get_eq_getElem] using (List.ofFn_getElem (xs:=terms a r sel bits))
  conv_rhs=>unfold mass;rw [←h]
  simp only [List.map_ofFn,List.sum_ofFn,bitInt_eq_toNat,Function.comp_apply]

theorem shifted_modulo (z : Int) (p offset : Nat) (hp : 0<p) (ho : offset<p) :
    (z-(offset : Int))%(p : Int)=0 ↔ (z%(p : Int)).toNat=offset:=by
  have hp' : (0 : Int)<p:=by exact_mod_cast hp
  have ho' : (offset : Int)<p:=by exact_mod_cast ho
  rw [←Int.emod_eq_emod_iff_emod_sub_eq_zero,
    Int.emod_eq_of_lt (Int.natCast_nonneg _) ho']
  constructor
  · intro h;exact_mod_cast congrArg Int.toNat h
  · intro h
    have h':=congrArg (fun n : Nat=>(n : Int)) h
    simpa only [Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hp'))] using h'

theorem modularOffset_consumer (I : Finset (Fin r.q)) (x : BitInput r.q)
    {cutoff : Nat} (prime : PrimeIndex cutoff) (offset : Fin prime.val) :
    modularEquationHolds
      (equation a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x) offset.val)
      prime (input a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x))=
      decide (LiveRows.modularOffset (thresholdFourfoldOccurrences r) I x
        (ThresholdRows.equation a r sel) prime.val=offset.val):=by
  unfold modularEquationHolds
  apply decide_eq_decide.mpr
  unfold LabelledEquation.HoldsModulo
  rw [expanded_difference]
  rw [shifted_modulo _ _ _ (mem_primesUpTo.mp prime.property).1.pos offset.isLt]
  simp only [LiveRows.modularOffset,LabelledEquation.difference,LabelledEquation.score,bitInt_eq_toNat]

end
end PCJ45bee56da9f34d5a_ExpandedThresholdStream
