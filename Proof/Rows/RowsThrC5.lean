import Proof.Rows.RowsThrSelBase

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrC5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeyTop RowsConstruction.ThrKey
open RowsConstruction.ThrSel RowsConstruction.ThrSelCasc RowsConstruction.ThrSelBase
noncomputable section

/-- **THR C5** (one fixed machine). -/
def thrC5 (NI : Nat) (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) :=
  thrTop NI (thrKey NI ini (selK NI ix ib iOne))

def keyCostU (w Rp R nK : Nat) : Nat :=
  (2*Rp+2+1+(2*Rp+4))+1+((4*w+4)+1+((2*(2*w+1)+2)+1+((2*(2*w+1)+2)+1+
    ((2*(2*w+1)+2)+1+(((2*R+4)+1+nK)+2)))))

/-- The uniform per-row cost of THR C5. -/
def c5Cost (wT RT wS SS Rp T F : Nat) : Nat :=
  carryCost wT RT (carryCost wS SS (keyCostU wT Rp RT (selCost T RT F wT)))

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- **THR C5 on the work block.** For every row `j` of the THR family, the fixed machine `thrC5` runs from `thrBase j` to
`thrBase (j+1)` (all heads `0`) at the uniform cost `c5Cost`, given the resident `init` words of the prime stage
(`psInit`), the selection cascade (`fb T (bnd c)`) and the base stage (`baseInit`, `scalar U (w+2) 1`). -/
theorem thr_c5 (j : Nat) (hj : j < (KeySucc.keys a r L target).length)
    (ini : Fin 40 → Fin NI) (hini : Function.Injective ini) (Rp Lp : Nat)
    (hinit : ∀ m, init (ini m) = psInit (wT a r four L target) Rp Lp m)
    (hRp : ∀ p, p ≤ KeySucc.cut a r target →
      RowsConstruction.ThrPrime.psCost (wT a r four L target) (KeySucc.cut a r target) p + 1 ≤ Rp)
    (hL : Rp + 1 ≤ Lp)
    (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hib : Function.Injective ib) (hone : ib 9 ≠ iOne)
    (hinitD : ∀ c, init (ix c) = fb (ThrWidth.T a r four L target) (bnd a r c))
    (hinitB : ∀ k : Fin 82, ¬ (73 ≤ k.val ∧ k.val < 77) → init (ib k) = baseInit a r four L target k)
    (hinitO : init iOne = ZeroPadding.pad (bU (ThrWidth.T a r four L target)) (fb (wT a r four L target) 1)) :
    Step (thrC5 NI ini ix ib iOne)
      (c5Cost (wT a r four L target) (RT a r four L target) (natBitLength (NS a r L target))
        (seedScratch (NS a r L target)) Rp (ThrWidth.T a r four L target) (bF (ThrWidth.T a r four L target)))
      (fun _ => 0) (thrBase a r four L target NI pub init rcp C cC hF j) (fun _ => 0)
      (thrBase a r four L target NI pub init rcp C cC hF (j+1)) := by
  refine thr_top a r four L target NI pub init rcp C cC hF j hj _ _ (fun h1 h2 => ?_)
  have hp : (KeySucc.keys a r L target)[j].prime.val ≤ KeySucc.cut a r target :=
    (mem_primesUpTo.mp (KeySucc.keys a r L target)[j].prime.property).2
  have hR := hRp _ hp
  have s := thr_key a r four L target NI pub init rcp C cC hF j hj h1 h2 ini hini Rp Lp hinit hR hL _ _
    (thr_sel a r four L target NI pub init rcp C cC hF j hj h1 h2 ix ib iOne hib hone hinitD hinitB hinitO)
  exact s.enlarge (by unfold keyCost keyCostU; omega)

end Thr

end
end RowsConstruction.ThrC5
