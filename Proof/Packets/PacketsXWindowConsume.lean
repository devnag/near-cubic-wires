import Proof.Packets.PacketsXWindowBoundedPolynomial

/-! Close the actual emitted window, physically rewind it, run the exact
bounded polynomial pipeline and return the outer-loop driver to head zero. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (cacheWord)
open NormalizedFiniteTransport WindowNativeOrder SubstitutionCensus Theorem25Completion.CycleBounds

theorem padded_terminator (R : Nat) (body : List Bool) (h : body.length+1≤R) :
    ZeroPadding.pad R body=ZeroPadding.pad R (body++[false]) := by
  unfold ZeroPadding.pad
  simp only [List.length_append,List.length_singleton,List.append_assoc]
  rw [show ([false] : List Bool)=List.replicate 1 false by rfl,←List.replicate_add]
  congr 2
  omega

theorem close_existing (R : Nat) (body : List Bool) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hh : H 78=body.length) (ha : A 78=ZeroPadding.pad R (body++[false]))
    (hw : H 31=1) (aw : A 31=UnaryTemplate.tape R) (hfit : body.length+1≤R) :
    Step closeSource (2*R+4) H A (Function.update H 78 0) A := by
  have h:=close_source_run R body H A hh (ha.trans (padded_terminator R body hfit).symm) hw aw hfit
  apply h.congr rfl
  rw [←ha,Function.update_eq_self]

noncomputable def lower := PhysicalIndexReload.move (95 : Fin 256) .left

attribute [local irreducible] closeSource polynomial lower

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
