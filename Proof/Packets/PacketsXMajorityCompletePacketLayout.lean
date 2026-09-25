import Proof.Packets.PacketsXSubstitutionNat
import Proof.Packets.PacketsXPacketEngineBoundary

/-! A fixed45-tape row-packet arena shares the existing arithmetic34 core,
retains the actual substitution atom bank and appends its native result on44. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

def extras (R : Nat) (atoms out : List Bool) : Fin 11→List Bool :=
  Fin.append (fun i : Fin 10=>if i=0 then atoms else List.replicate R false)
    (fun _ : Fin 1=>out)
def heads (out : List Bool) : Fin 45→Nat :=
  Fin.append ReusableArithmetic.heads (Fin.append (fun _ : Fin 10=>0) (fun _ : Fin 1=>out.length))
def bank (C R : Nat) (left right : Ring.Poly Nat) (atoms out : List Bool) : Fin 45→List Bool :=
  Fin.append (ReusableArithmetic.natState C R left right) (extras R atoms out)
def coldBank (C R : Nat) (left right : Ring.Poly Nat) (atoms out : List Bool) : Fin 45→List Bool :=
  Fin.append (SubstitutionCall.coldResident C R (left.map (maskNat C)) (right.map (maskNat C)) atoms)
    (fun _ : Fin 1=>out)
def normalizeSlots (i : Fin 34) : Fin 45 := i.castAdd 11
def serializeSlots : Fin 35→Fin 45 :=
  Fin.append normalizeSlots (fun _ : Fin 1=>44)
def lower := TapeEmbedding.machine 1 SubstitutionCall.coldExecute
def normalize := RecoveryFocus.machine normalizeSlots PacketOuterNormalize.machine
def serialize := RecoveryFocus.machine serializeSlots Theorem25Completion.CycleFlatDock.machine

theorem normalize_injective : Function.Injective normalizeSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 45=>z.val) h)
theorem serialize_injective : Function.Injective serializeSlots := by decide

theorem heads_embed (out : List Bool) :
    Fin.append SubstitutionCall.heads (fun _ : Fin 1=>out.length)=heads out := by
  change Fin.append (Fin.append _ _) _=_
  rw [Fin.append_assoc]
  rfl

theorem bank_embed (C R : Nat) (left right : Ring.Poly Nat) (atoms out : List Bool) :
    Fin.append (SubstitutionCall.resident C R (left.map (maskNat C)) (right.map (maskNat C)) atoms)
      (fun _ : Fin 1=>out)=bank C R left right atoms out := by
  change Fin.append (Fin.append _ _) _=_
  rw [Fin.append_assoc]
  rfl

theorem normalize_run (C w : Nat) (left P : Ring.Poly Nat) (atoms out : List Bool)
    (hw : 1≤w) (hP : Ring.Normal P) (hf : Fits C P)
    (hl : left.length≤2^w) (hc : P.length≤2^w) :
    Step normalize (PacketOuterNormalize.budget C (commonReserve C w) P)
      (heads out) (bank C (commonReserve C w) left P atoms out)
      (heads out) (bank C (commonReserve C w) [] (Ring.norm P) atoms out) := by
  apply PhysicalFocusBoundary.focus (PacketOuterNormalize.run C w left P hw hP hf hl hc)
    normalizeSlots normalize_injective
  · intro i;simp only [heads,normalizeSlots,Fin.append,Fin.addCases_left]
  · intro i;simp only [bank,normalizeSlots,Fin.append,Fin.addCases_left]
  · intro i;simp only [heads,normalizeSlots,Fin.append,Fin.addCases_left]
  · intro i;simp only [bank,normalizeSlots,Fin.append,Fin.addCases_left]
  · intro i away
    revert away
    refine Fin.addCases (m:=34) (n:=11) (fun j=>?_) (fun j=>?_) i
    · intro away;exact False.elim (away j rfl)
    · intro _;exact ⟨rfl,by simp only [bank,Fin.append,Fin.addCases_right]⟩

theorem serialize_heads (out : List Bool) (i : Fin 35) :
    heads out (serializeSlots i)=Theorem25Completion.CycleFlatDock.heads out i := by
  refine Fin.addCases (m:=34) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [serializeSlots,Fin.addCases_left,heads,normalizeSlots,Fin.append,Fin.addCases_left]
    exact congrFun (PacketEngineBoundary.heads_flat out) j
  · fin_cases j;rfl

theorem serialize_bank (C R : Nat) (P : Ring.Poly Nat) (atoms out : List Bool)
    (hR : 1≤R) (i : Fin 35) :
    bank C R [] P atoms out (serializeSlots i)=
      Theorem25Completion.CycleFlatDock.bank C R [] 0 (P.map (maskNat C)) out i := by
  refine Fin.addCases (m:=34) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [serializeSlots,Fin.addCases_left,bank,normalizeSlots,Fin.append,Fin.addCases_left]
    exact congrFun (PacketEngineBoundary.state_flat C R [] (P.map (maskNat C)) out hR) j
  · fin_cases j;rfl

theorem serialize_run (C w : Nat) (P : Ring.Poly Nat) (atoms out : List Bool)
    (hf : Fits C P) (hn : Ring.Normal P) (hc : P.length≤2^w) :
    Step serialize (2*(P.length*(C^2+8*C+9)+8)+2*commonReserve C w+7)
      (heads out) (bank C (commonReserve C w) [] P atoms out)
      (heads (out++ExtIncidence.stream P))
      (bank C (commonReserve C w) [] [] atoms (out++ExtIncidence.stream P)) := by
  have hR : 1≤commonReserve C w := by
    have h:=(Theorem25Completion.CycleDenseAtomCost.reserve_small C w).1
    omega
  apply PhysicalFocusBoundary.focus (PacketNativeMeaning.run C w [] 0 P out hf hn hc)
    serializeSlots serialize_injective
  · intro i;exact (serialize_heads out i).symm
  · intro i;exact (serialize_bank C (commonReserve C w) P atoms out hR i).symm
  · intro i;exact (serialize_heads (out++ExtIncidence.stream P) i).symm
  · intro i;exact (serialize_bank C (commonReserve C w) [] atoms (out++ExtIncidence.stream P) hR i).symm
  · intro i away
    revert away
    refine Fin.addCases (m:=34) (n:=11) (fun j=>?_) (fun j=>?_) i
    · intro away;exact False.elim (away (j.castAdd 1) (by simp only [serializeSlots,Fin.append,Fin.addCases_left];rfl))
    · refine Fin.addCases (m:=10) (n:=1) (fun k=>?_) (fun k=>?_) j
      · intro _;exact ⟨by simp only [heads,Fin.append,Fin.addCases_right,Fin.addCases_left],
          by simp only [bank,extras,Fin.append,Fin.addCases_right,Fin.addCases_left]⟩
      · fin_cases k
        intro away
        exact False.elim (away 34 rfl)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketRun
