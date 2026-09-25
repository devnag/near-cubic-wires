import Proof.SourceAssembly.AdmissionSource
import Proof.SourceAssembly.SourceSkelInitK

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SelCapS
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer)
noncomputable section

section any
variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) {n : Nat} (x : BitInput n) (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) (bits : List Bool)
  (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (hden : 1 ≤ den)
  (cL eL cP eP : Nat) (h4 : 4 ≤ cL)
  (hdesc : Admission.symDescCap p.clauseDegree (req sources k clock x oracle).arity ≤
    SourceBudget.ldCap cL eL (req sources k clock x oracle).arity)
  (hP : SourceSkeleton.Params.pSum cL eL (req sources k clock x oracle).arity ≤
    cP * ((req sources k clock x oracle).arity + 1) ^ eP)

include h4 in
theorem four_le_ld (q : Nat) : 4 ≤ SourceBudget.ldCap cL eL q := by
  unfold SourceBudget.ldCap
  have h1 : 1 ≤ (q+1)^eL := Nat.one_le_pow _ _ (Nat.succ_pos q)
  calc 4 ≤ cL := h4
    _ = cL * 1 := (Nat.mul_one cL).symm
    _ ≤ cL * (q+1)^eL := Nat.mul_le_mul_left cL h1

theorem cube_le_wCap (q : Nat) : q ^ 3 ≤ SourceBudget.wCap q := by
  unfold SourceBudget.wCap
  exact Nat.pow_le_pow_left (Nat.le_succ q) 3

include hN hden h4 hdesc hP in

theorem thr_caps :
    ∀ j, ∀ mo ∈ (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).monomials, ∀ cc,
      C10TotalDecode.Atom.threshold cc ∈ mo.factors →
      4 ≤ SourceBudget.ldCap cL eL (req sources k clock x oracle).arity ∧
      cc.descriptionBits ≤ SourceBudget.ldCap cL eL (req sources k clock x oracle).arity ∧
      cc.wireCount ≤ SourceBudget.wCap (req sources k clock x oracle).arity ∧
      RepairOrdinary.CloseoutRowsCircuitCapacity.capacity (SourceRequest.ThrSwitch.codeWidth
        (SourceBudget.ldCap cL eL (req sources k clock x oracle).arity)) ≤ cP * ((req sources k clock x oracle).arity + 1) ^ eP := by
  intro j mo hmo cc hcc
  have hadm := Admission.coordinate_admitted sources k clock p den x oracle bits hN j mo hmo _ hcc
  obtain ⟨hw, hd⟩ := hadm
  have he := (Admission.carried_descriptions_le_envelope hden p.clauseDegree (req sources k clock x oracle).arity).2
  have hs : CloseoutRawRows.descriptionEnvelope p.clauseDegree (req sources k clock x oracle).arity ≤
      Admission.symDescCap p.clauseDegree (req sources k clock x oracle).arity := by
    unfold Admission.symDescCap; exact Nat.le_add_right _ _
  have hc := Admission.carriedWireCap_le_cube hden 9 (req sources k clock x oracle).arity
  have hq := cube_le_wCap (req sources k clock x oracle).arity
  have hp : RepairOrdinary.CloseoutRowsCircuitCapacity.capacity (SourceRequest.ThrSwitch.codeWidth
      (SourceBudget.ldCap cL eL (req sources k clock x oracle).arity)) ≤
      SourceSkeleton.Params.pSum cL eL (req sources k clock x oracle).arity := by
    unfold SourceSkeleton.Params.pSum SourceBudget.pCap; exact Nat.le_add_right _ _
  exact ⟨four_le_ld cL eL h4 _, hd.trans (he.trans (hs.trans hdesc)), hw.trans (hc.trans hq), hp.trans hP⟩

include hN hden h4 hdesc hP in

theorem sym_caps :
    ∀ j, ∀ mo ∈ (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).monomials, ∀ cc,
      C10TotalDecode.Atom.symmetric cc ∈ mo.factors →
      4 ≤ SourceBudget.ldCap cL eL (req sources k clock x oracle).arity ∧
      cc.descriptionBits ≤ SourceBudget.ldCap cL eL (req sources k clock x oracle).arity ∧
      cc.wireCount ≤ SourceBudget.wCap (req sources k clock x oracle).arity ∧
      RepairOrdinary.CloseoutRowsCircuitCapacity.capacity (SourceRequest.SymOriginal.symCodeWidth
        (SourceBudget.ldCap cL eL (req sources k clock x oracle).arity)) ≤ cP * ((req sources k clock x oracle).arity + 1) ^ eP := by
  intro j mo hmo cc hcc
  have hadm := Admission.coordinate_admitted sources k clock p den x oracle bits hN j mo hmo _ hcc
  obtain ⟨hw, hd⟩ := hadm
  have he := (Admission.carried_descriptions_le_envelope hden p.clauseDegree (req sources k clock x oracle).arity).1
  have hs : CloseoutRawRows.descriptionEnvelope p.clauseDegree (req sources k clock x oracle).arity ≤
      Admission.symDescCap p.clauseDegree (req sources k clock x oracle).arity := by
    unfold Admission.symDescCap; exact Nat.le_add_right _ _
  have hc := Admission.carriedWireCap_le_cube hden 5 (req sources k clock x oracle).arity
  have hq := cube_le_wCap (req sources k clock x oracle).arity
  have hp : RepairOrdinary.CloseoutRowsCircuitCapacity.capacity (SourceRequest.SymOriginal.symCodeWidth
      (SourceBudget.ldCap cL eL (req sources k clock x oracle).arity)) ≤
      SourceSkeleton.Params.pSum cL eL (req sources k clock x oracle).arity := by
    unfold SourceSkeleton.Params.pSum SourceBudget.pCap; exact Nat.le_add_left _ _
  exact ⟨four_le_ld cL eL h4 _, hd.trans (he.trans (hs.trans hdesc)), hw.trans (hc.trans hq), hp.trans hP⟩

end any

theorem hcap_site (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (den : Nat) {n : Nat} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) (bits : List Bool)
    (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (hden : 1 ≤ den) (mode : Bool) :
    if mode then (∀ j, ∀ mo ∈ (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).monomials, ∀ cc,
      C10TotalDecode.Atom.symmetric cc ∈ mo.factors →
      4 ≤ SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p)
        (req sources k clock x oracle).arity ∧
      cc.descriptionBits ≤ SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p)
        (req sources k clock x oracle).arity ∧
      cc.wireCount ≤ SourceBudget.wCap (req sources k clock x oracle).arity ∧
      RepairOrdinary.CloseoutRowsCircuitCapacity.capacity (SourceRequest.SymOriginal.symCodeWidth
        (SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p)
          (req sources k clock x oracle).arity)) ≤
        SourceSkeleton.Params.pC sources gamma hg hh p * ((req sources k clock x oracle).arity + 1) ^ SourceSkeleton.Params.pE sources gamma hg hh p)
    else (∀ j, ∀ mo ∈ (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).monomials, ∀ cc,
      C10TotalDecode.Atom.threshold cc ∈ mo.factors →
      4 ≤ SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p)
        (req sources k clock x oracle).arity ∧
      cc.descriptionBits ≤ SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p)
        (req sources k clock x oracle).arity ∧
      cc.wireCount ≤ SourceBudget.wCap (req sources k clock x oracle).arity ∧
      RepairOrdinary.CloseoutRowsCircuitCapacity.capacity (SourceRequest.ThrSwitch.codeWidth
        (SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p)
          (req sources k clock x oracle).arity)) ≤
        SourceSkeleton.Params.pC sources gamma hg hh p * ((req sources k clock x oracle).arity + 1) ^ SourceSkeleton.Params.pE sources gamma hg hh p) := by
  have h4 := SourceSkeleton.Params.ldC_ge sources gamma hg hh p
  have hdesc := SourceSkeleton.Params.symDescCap_le_ld sources gamma hg hh p (req sources k clock x oracle).arity
  have hP := SourceSkeleton.Params.pSum_le_P sources gamma hg hh p (req sources k clock x oracle).arity
  cases mode with
  | false => exact thr_caps sources k clock p den x oracle bits hN hden _ _ _ _ h4 hdesc hP
  | true => exact sym_caps sources k clock p den x oracle bits hN hden _ _ _ _ h4 hdesc hP

end
end NearCubicWires.SourceRequest.SelCapS

