import Proof.SourceAssembly.SourceSkelInitAll
import Proof.SourceAssembly.SourceFirstFront3

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

def initResVal (Rc q L CP DP CW DW CL DL : Nat) (mode : Bool) (tg : Nat) (val : Nat → Option (List Bool)) (i : Nat) :
    List Bool :=
  if i = 0 then ZeroPadding.pad Rc (UnaryTemplate.tape q)
  else if i = 1 then ZeroPadding.pad Rc (List.replicate (CP*(q+1)^DP) true)
  else if i = 2 then ZeroPadding.pad Rc (List.replicate (CW*(q+1)^DW) true)
  else if i = 3 then ZeroPadding.pad Rc (List.replicate (CL*(q+1)^DL) true)
  else if i = 4 then ZeroPadding.pad Rc (SourceFactorSel.Nat.tagWord mode)
  else if i = 5 then ZeroPadding.pad Rc (frame (natWord q))
  else if i = 6 then ZeroPadding.pad Rc (frame (natWord L))
  else if i = 7 then ZeroPadding.pad Rc (frame (natWord tg))
  else slotVal Rc val i

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-- **Every strip resident, read back** (`i < NR`): `initResVal … i`, head 0. -/
theorem inv_resident {NR NE : Nat} (hNR : NR ≤ 32) {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (i : Nat) (hiN : i < NR) :
    A' (stripT pl hh i (by omega)) = initResVal Rc q L CP DP CW DW CL DL mode tg val i ∧
      H' (stripT pl hh i (by omega)) = 0 := by
  have vs : (stripT pl hh i (by omega)).val = sb d eX pX gW + i := rfl
  by_cases h8 : 8 ≤ i
  · have := hi.strip (stripT pl hh i (by omega)) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + i - sb d eX pX gW = i by omega] at this
    rw [this.1]
    refine ⟨?_, this.2⟩
    unfold initResVal
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · obtain ⟨H1, A1, ho, hag⟩ := hi.base
    have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
    have ag := hag (stripT pl hh i (by omega)) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [ag.1, ag.2]
    have e : ∀ k : Fin 12, k.val = i → stripT pl hh i (by omega) = Dims.hrT (ext3 pl hh) pl.hT k :=
      fun k hk => Fin.ext (by rw [vs, Dims.hrT_val, hk])
    unfold initResVal
    interval_cases i
    · rw [e 0 rfl]; simpa using ho.z0
    · rw [e 1 rfl]; simpa using ho.z1
    · rw [e 2 rfl]; simpa using ho.z2
    · rw [e 3 rfl]; simpa using ho.z3
    · rw [e 4 rfl]; simpa using ho.z4
    · rw [e 5 rfl]; simpa using ho.z5
    · rw [e 6 rfl]; simpa using ho.z6
    · rw [e 7 rfl]; simpa using ho.z7

end
end NearCubicWires.SourceSkeleton.InitS
end
