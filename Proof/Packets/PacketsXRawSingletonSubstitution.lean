import Proof.CaseAnalysis.RowsEstimatorSubstitutionBounded
import Proof.Rows.PhysicalFocusBoundary

/-! Reusable raw singleton substitution on a physically allocated bank.
The original executed substitution is followed by a paid reset of every
cursor; its private words already return to the same padded zero backing. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.RawSingletonSubstitution
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (Pair cacheWord)

noncomputable def machine := MaskedReset.machine CloseoutRowsEstimator.SubstitutionOuter.machine (fun _=>true)
def pads (R : Nat) (i : Fin 11) := if i=1 then 0 else R
def words (R : Nat) (source cache out : List Bool) : Fin 11→List Bool :=
  ![ZeroPadding.pad R source,cache,List.replicate R false,List.replicate R false,
    List.replicate R false,List.replicate R false,List.replicate R false,
    List.replicate R false,List.replicate R false,List.replicate R false,ZeroPadding.pad R out]
def bank (R : Nat) (source cache out : List Bool) : Fin 12→List Bool :=
  Fin.addCases (m:=11) (n:=1) (motive:=fun _=>List Bool)
    (words R source cache out) (fun _ : Fin 1=>List.replicate (R+3) false)
def budget (cs : List Pair) (d rows : Nat) := 2*CloseoutRowsEstimator.SubstitutionBounds.fuel cs 1 d rows+2

theorem padded_data (S R : Nat) (source cache out : List Bool) (hS : S≤R) (hR : 1≤R) :
    (fun i=>ZeroPadding.pad (pads R i) (CloseoutRowsEstimator.SubstitutionOuter.data S source cache [] out i))=
      words R source cache out := by
  have hz : ZeroPadding.pad R (List.replicate S false)=List.replicate R false := by
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hS]
  have ho : ZeroPadding.pad R [false]=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  have he : ZeroPadding.pad S ([] : List Bool)=List.replicate S false := by simp [ZeroPadding.pad]
  funext i
  fin_cases i <;>simp [pads,words,CloseoutRowsEstimator.SubstitutionOuter.data,
    CloseoutRowsEstimator.SubstitutionFactor.data,Fin.addCases,hz,ho,he]

theorem run (R d : Nat) (cs : List Pair)
    (hc : ∀ i (hi : i<cs.length),(cs[i].1++cs[i].2).length≤1)
    (P : StructuralGF2Polynomial) (hv : CloseoutRowsEstimator.SubstitutionOuter.Valid cs P)
    (hd : ∀ m∈P,m.length≤d) (hR : 1≤R)
    (hspace : CloseoutRowsEstimator.SubstitutionBounds.space cs 1 d (cacheWord cs).length≤R)
    (hcost : CloseoutRowsEstimator.SubstitutionBounds.fuel cs 1 d P.length≤R+3) :
    Step machine (budget cs d P.length) (fun _=>0) (bank R (ExtIncidence.stream P) (cacheWord cs) [])
      (fun _=>0) (bank R (ExtIncidence.stream P) (cacheWord cs)
        (ExtIncidence.stream (structuralGF2Substitute (CloseoutRowsEstimator.SubstitutionMonomial.atom cs) P))) := by
  obtain ⟨hb,h⟩:=CloseoutRowsEstimator.SubstitutionBounds.bounded_run cs 1 d (by decide) hc P hv hd [] [] []
  have padded:=(h.enlarge hb).pad (pads R)
  have reset:=padded.mask (fun _=>true) (by intro i _;fin_cases i <;>rfl) hcost
  apply (reset.congr_in ?_ ?_).congr ?_ ?_
  · funext i;fin_cases i <;>rfl
  · simp only [List.nil_append,List.append_nil,padded_data _ R _ _ _ hspace hR]
    rfl
  · funext i;fin_cases i <;>rfl
  · simp only [List.nil_append,List.append_nil,padded_data _ R _ _ _ hspace hR]
    rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.RawSingletonSubstitution
