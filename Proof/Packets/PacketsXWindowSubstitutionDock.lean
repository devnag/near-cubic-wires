import Proof.Packets.WindowProviderPorts
import Proof.Packets.PacketsXSubstitutionNat

/-! The reusable normalized substitution executes inside the actual provider
arena and preserves every field except the two arithmetic operands. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport SubstitutionCensus SubstitutionInvariant
open Theorem25Completion.CycleBounds
open NearCubicWires.RepairSource.VerifierDecoding

def operands (R : Nat) (left right : List (List Bool)) (A : Fin 256→List Bool) :=
  Function.update (Function.update (Function.update (Function.update A
    25 (ZeroPadding.pad R left.flatten)) 28 (ZeroPadding.pad R (CompareMachine.word left.length)))
    26 (ZeroPadding.pad R right.flatten)) 27 (ZeroPadding.pad R (CompareMachine.word right.length))

theorem state_outside (C R : Nat) (left right left' right' : List (List Bool))
    (i : Fin 34) (h25 : i≠25) (h26 : i≠26) (h27 : i≠27) (h28 : i≠28) :
    ReusableArithmetic.state C R left' right' i=ReusableArithmetic.state C R left right i := by
  have a:=VectorAccumulator.tapes_left_outside C R left right' left' [] (i.castAdd 2)
    (by intro he;apply h25;exact Fin.ext (congrArg (fun x : Fin 36=>x.val) he))
    (by intro he;apply h28;exact Fin.ext (congrArg (fun x : Fin 36=>x.val) he))
  have b:=VectorAccumulator.tapes_right_outside C R left right right' [] (i.castAdd 2)
    (by intro he;apply h26;exact Fin.ext (congrArg (fun x : Fin 36=>x.val) he))
    (by intro he;apply h27;exact Fin.ext (congrArg (fun x : Fin 36=>x.val) he))
  simp only [VectorAccumulator.tapes_engine] at a b
  exact a.symm.trans b.symm

theorem substitution_result (C R : Nat) (left right left' right' : List (List Bool))
    (atoms : List Bool) (A : Fin 256→List Bool)
    (ha : ∀ i,A (substitutionPorts i)=SubstitutionCall.resident C R left right atoms i) :
    ∀ i,SubstitutionCall.resident C R left' right' atoms i=
      operands R left' right' A (substitutionPorts i) := by
  intro i
  refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
  · by_cases h25 : j=25
    · subst j;rfl
    by_cases h26 : j=26
    · subst j;rfl
    by_cases h27 : j=27
    · subst j;rfl
    by_cases h28 : j=28
    · subst j;rfl
    have ne (k : Fin 34) (h : j≠k) : substitutionPorts (j.castAdd 10)≠k.castAdd 222 := by
      intro he
      apply h
      apply Fin.ext
      have he':=congrArg (fun x : Fin 256=>x.val) he
      simpa only [substitutionPorts,Fin.addCases_left,Fin.val_castAdd] using he'
    have hn25 : substitutionPorts (j.castAdd 10)≠25:=ne 25 h25
    have hn26 : substitutionPorts (j.castAdd 10)≠26:=ne 26 h26
    have hn27 : substitutionPorts (j.castAdd 10)≠27:=ne 27 h27
    have hn28 : substitutionPorts (j.castAdd 10)≠28:=ne 28 h28
    simp only [operands,Function.update_of_ne hn25,Function.update_of_ne hn26,
      Function.update_of_ne hn27,Function.update_of_ne hn28]
    rw [SubstitutionCall.resident_core]
    have hj:=ha (j.castAdd 10)
    rw [SubstitutionCall.resident_core] at hj
    exact (state_outside C R left right left' right' j h25 h26 h27 h28).trans hj.symm
  · have ne (k : Fin 256) (hk : k.val<34) : substitutionPorts (j.natAdd 34)≠k := by
      intro he
      have h:=congrArg Fin.val he
      simp only [substitutionPorts,Fin.addCases_right] at h
      fin_cases j <;>dsimp at h <;>omega
    simp only [operands,Function.update_of_ne (ne 25 (by decide)),Function.update_of_ne (ne 26 (by decide)),
      Function.update_of_ne (ne 27 (by decide)),Function.update_of_ne (ne 28 (by decide))]
    simpa only [SubstitutionCall.resident_extra] using (ha (j.natAdd 34)).symm

noncomputable def substitute := RecoveryFocus.machine substitutionPorts SubstitutionCall.execute

theorem substitute_run (C w d : Nat) (S : Finset Nat) (hS : ∀ j∈S,j<C)
    (hw : 1≤w) (hfit : (S.card+1)^d≤2^w) (hfitAtom : S.card+1≤2^w)
    (P : Ring.Poly Nat) (hP : Good C P) (hdeg : Ring.Degree d P) (hcount : P.length≤2^w)
    (atoms : List (Ring.Poly Nat)) (hlen : atoms.length=C) (ha : ∀ Q∈atoms,Bounded S 1 Q)
    (left : Ring.Poly Nat) (hl : left.length≤2^w)
    (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hh : ∀ i,SubstitutionCall.heads i=H (substitutionPorts i))
    (bank : ∀ i,A (substitutionPorts i)=SubstitutionCall.resident C (commonReserve C w)
      (left.map (maskNat C)) (P.map (maskNat C)) (PacketVector.bank (commonReserve C w) (SubstitutionOuter.atomMasks C atoms)) i) :
    Step substitute (SubstitutionCall.totalBudget C (commonReserve C w) P.length) H A H
      (operands (commonReserve C w) ((SubstitutionCall.leftResult atoms P left).map (maskNat C))
        ((Normalized.structuralGF2Substitute (fun code=>atoms.getD code []) P).map (maskNat C)) A) := by
  apply PhysicalFocusBoundary.focus (SubstitutionCall.nat_run C w d S hS hw hfit hfitAtom P hP hdeg hcount
    atoms hlen ha left hl) substitutionPorts substitution_injective H H A _ hh
    (fun i=>(bank i).symm) hh
    (substitution_result C (commonReserve C w) _ _ _ _ _ A bank)
  intro i away
  have h25 : i≠25 := by intro he;subst i;exact away 25 rfl
  have h26 : i≠26 := by intro he;subst i;exact away 26 rfl
  have h27 : i≠27 := by intro he;subst i;exact away 27 rfl
  have h28 : i≠28 := by intro he;subst i;exact away 28 rfl
  exact ⟨rfl,by simp only [operands,Function.update_of_ne h25,Function.update_of_ne h26,
    Function.update_of_ne h27,Function.update_of_ne h28]⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
