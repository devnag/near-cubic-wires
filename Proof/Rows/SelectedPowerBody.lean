import Proof.Rows.SelectedPowerBank

/-! Consume the physically selected native child in the existing scaled mapper,
update the factor, and clear only the consumed native child buffer. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ45bee56da9f34d5a_SelectedPowerBank
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_PowerEquation.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_HeaderRewind.clear

def equation {n : Nat} (g : ExactThresholdGate n):SupplierPipeline.LabelledEquation (Fin n):={weights:=g.weight,target:=g.target}
def emit:=TapeEmbedding.machine 5 PCJ45bee56da9f34d5a_PowerEquation.machine
def clearSlots:Fin 3→Fin 99:=![65,62,63]
def clear:=RecoveryFocus.machine clearSlots (PCJ45bee56da9f34d5a_HeaderRewind.clear 1)

theorem source_eq {n : Nat} (g : ExactThresholdGate n):
 PCJ45bee56da9f34d5a_NativeScaleEquation.source (equation g)=exactWord g :=rfl

theorem emit_run {n : Nat} (g : ExactThresholdGate n) (a B p w F U index : Nat) (source out : List Bool)
 (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w) (hB : B<2^w)
 (hw : ∀j,C10NativeResidueCallback.coreBudget false (g.weight j) w+1≤F)
 (ht : C10NativeResidueCallback.coreBudget true g.target w+1≤F)
 (hU : 1024*(w+1)^2+2≤U) :
 Step emit (PCJ45bee56da9f34d5a_NativeScaleEquation.budget n F w U g.target+1+(1024*(w+1)^2+10*U+18*w+45))
  (heads 0 out.length) (bank a B p w F U n index source (exactWord g) out)
  (heads (exactWord g).length (out.length+(n+1)*(2*w+1)))
  (bank ((a*B)%p) B p w F U n index source (exactWord g)
    (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation g))) :=by
 have h:=(PCJ45bee56da9f34d5a_PowerEquation.run [] [] out a B p w F U (equation g) hp hpw ha hB hw ht hU).pad (caps U)
 simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,source_eq] at h
 exact h.embed (![0,1,0,0,0] :Fin 5→Nat) (extras source index U)

theorem heads_away (pos pos' len : Nat) (i : Fin 99) (hi : i≠65):heads pos len i=heads pos' len i :=by
 fin_cases i <;>first | exact False.elim (hi rfl) | rfl

theorem clear_run (a B p w F U n index : Nat) (source bits out : List Bool) (hb : bits.length≤U) :
 Step clear (4*U+9) (heads bits.length out.length) (bank a B p w F U n index source bits out)
  (heads 0 out.length) (bank a B p w F U n index source [] out) :=by
 have h:=(PCJ45bee56da9f34d5a_HeaderRewind.clear_run 1 (fun _ :Fin 1=>bits.length)
  (fun _ :Fin 1=>ZeroPadding.pad U bits) U (fun _=>hb)
  (by intro i;rw [ZeroPadding.pad_length];exact max_le (le_refl _) hb)).dock clearSlots (by decide)
  (heads bits.length out.length) (bank a B p w F U n index source bits out)
  (by intro i;fin_cases i <;>rfl)
  (by
   intro i;fin_cases i
   · exact at65 a B p w F U n index source bits out
   · exact at62 a B p w F U n index source bits out
   · exact at63 a B p w F U n index source bits out)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads clearSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact heads_away _ _ out.length i (fun he=>hi 0 he.symm)
 · apply HierarchyAllocation.install_eq clearSlots (by decide)
   · intro i;fin_cases i
     · rfl
     · exact at62 a B p w F U n index source [] out
     · exact at63 a B p w F U n index source [] out
   · intro i hi;exact (bits_away a B p w F U n index _ _ _ out i (fun he=>hi 0 he.symm)).symm
end
end PCJ45bee56da9f34d5a_SelectedPowerBody
