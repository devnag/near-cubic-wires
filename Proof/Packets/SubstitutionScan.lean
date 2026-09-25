import Proof.Packets.SubstitutionBit
import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.PacketVector

/-! The complete descending literal-bit product loop. Every iteration is the
actual decrement/read/lookup/multiply worker, driven by a resident unary width.
The step guards are the concrete reserve inequalities, not execution advice. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
abbrev Packet := List (List Bool)

def scan (C base : Nat) (source : List Bool) (atoms : List Packet) (left accumulator : Packet) :
    Nat→Packet×Packet
  | 0=>(left,accumulator)
  | k+1=>
    let prior:=scan C base source atoms left accumulator k
    let selected:=atoms.getD (C-(k+1)) []
    if readTapeBit source (base+(C-(k+1))) then
      (selected,NormalizerOrder.ordered (MaskProduct.unions selected prior.2)) else prior


/-- The descending physical scan realizes the exact right fold, including the
order-sensitive list representation of each normalized multiplication. -/
theorem scan_snd_eq_foldr (C base : Nat) (source : List Bool) (atoms : List Packet)
    (left accumulator : Packet) (k : Nat) (hk : k≤C) :
    (scan C base source atoms left accumulator k).2=
      (List.range' (C-k) k).foldr (fun j acc=>
        if readTapeBit source (base+j) then
          NormalizerOrder.ordered (MaskProduct.unions (atoms.getD j []) acc) else acc) accumulator := by
  induction k with
  | zero=>simp [scan]
  | succ k ih=>
    have hshift : C-(k+1)+1=C-k := by omega
    rw [List.range'_succ]
    simp only [List.foldr_cons,hshift,←ih (by omega),scan]
    cases readTapeBit source (base+(C-(k+1))) <;>rfl

theorem scan_complete (C base : Nat) (source : List Bool) (atoms : List Packet)
    (left accumulator : Packet) :
    (scan C base source atoms left accumulator C).2=
      (List.range' 0 C).foldr (fun j acc=>
        if readTapeBit source (base+j) then
          NormalizerOrder.ordered (MaskProduct.unions (atoms.getD j []) acc) else acc) accumulator := by
  simpa only [Nat.sub_self] using scan_snd_eq_foldr C base source atoms left accumulator C (Nat.le_refl C)

noncomputable def machine := RepeatMachine.machine SubstitutionBit.machine (fun _ _=>true)
def iterationBudget (R : Nat) := 80*(R+1)^2
def budget (C R : Nat) := C*(iterationBudget R+3)+3

theorem bit_budget (B R j : Nat) (selected accumulator : Packet)
    (hj : j≤R) (hc : NormalizedMultiply.budget B selected accumulator≤R) :
    SubstitutionBit.budget B R j selected accumulator≤ iterationBudget R := by
  have h:=SubstitutionAtom.budget_bound B R j selected accumulator hj hc
  unfold SubstitutionBit.budget iterationBudget
  nlinarith

variable (B C R base : Nat) (source : List Bool) (atoms : List Packet) (left accumulator : Packet)
variable (hlen : atoms.length=C) (hR : C+1≤R)
variable (hAtoms : ∀ P∈atoms,PacketVector.Fits R P ∧ ∀ bits∈P,bits.length=B)
variable (hstates : ∀ k, k<C→
    let p:=scan C base source atoms left accumulator k
    let selected:=atoms.getD (C-(k+1)) []
    PacketVector.Fits R p.1 ∧ (∀ bits∈p.2,bits.length=B) ∧
    (∀ i,(ReusableArithmetic.data B selected p.2 i).length≤R) ∧
    NormalizedMultiply.budget B selected p.2+3≤R)

def loopHeads (k : Nat) := SubstitutionBit.H (base+(C-k))
def loopData (k : Nat) :=
  let p:=scan C base source atoms left accumulator k
  SubstitutionBit.A B R (C-k) p.1 p.2 (PacketVector.bank R atoms) source

include hlen hR hAtoms hstates

theorem iteration (k : Nat) (hk : k<C) :
    Step SubstitutionBit.machine (iterationBudget R)
      (loopHeads C base k) (loopData B C R base source atoms left accumulator k)
      (loopHeads C base (k+1)) (loopData B C R base source atoms left accumulator (k+1)) := by
  let j:=C-(k+1)
  have hj : j<atoms.length := by dsimp [j];omega
  let selected:=atoms.getD j []
  have he : selected=atoms[j] := List.getD_eq_getElem atoms [] hj
  have hs:=hAtoms atoms[j] (List.getElem_mem hj)
  rw [←he] at hs
  obtain ⟨hl,ha,hi,hcap⟩ := hstates k hk
  let prior:=scan C base source atoms left accumulator k
  have countLeft : prior.1.length+1≤R := by
    simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using hl.2
  have countSelected : selected.length+1≤R := by
    simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using hs.1.2
  have hprefix : (PacketVector.bank R (atoms.take j)).length=2*j*R := by
    rw [PacketVector.bank_length R _ (fun P hP=>(hAtoms P (List.mem_of_mem_take hP)).1),List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  have splitBank := PacketVector.bank_split R atoms ⟨j,hj⟩
  change PacketVector.bank R atoms=PacketVector.bank R (atoms.take j)++
    ZeroPadding.pad R atoms[j].flatten++ZeroPadding.pad R (CompareMachine.word atoms[j].length)++
      PacketVector.bank R (atoms.drop (j+1)) at splitBank
  rw [←he] at splitBank
  have h:=SubstitutionBit.run B R j (base+j) prior.1 selected prior.2
    (PacketVector.bank R (atoms.take j)) (PacketVector.bank R (atoms.drop (j+1))) source
    hprefix hl.1 countLeft hs.1.1 countSelected hs.2 ha hi hcap (by dsimp [j];omega)
  dsimp only at h
  rw [←splitBank] at h
  have hc : C-k=j+1 := by dsimp [j];omega
  have endpoint : scan C base source atoms left accumulator (k+1)=
      (if readTapeBit source (base+j) then selected else prior.1,
       if readTapeBit source (base+j) then NormalizerOrder.ordered (MaskProduct.unions selected prior.2)
         else prior.2) := by
    change (if readTapeBit source (base+j) then _ else _) = _
    cases readTapeBit source (base+j) <;>rfl
  have cap : NormalizedMultiply.budget B selected prior.2+3≤R := hcap
  have bound:=bit_budget B R j selected prior.2 (by dsimp [j];omega) (by omega)
  have h':=h.enlarge bound
  simpa only [loopHeads,loopData,endpoint,hc,Nat.add_assoc] using h'

theorem run :
    Step machine (budget C R)
      (Fin.addCases (loopHeads C base 0) (fun _ : Fin 1=>1))
      (Fin.addCases (loopData B C R base source atoms left accumulator 0)
        (fun _ : Fin 1=>CompareMachine.word C))
      (Fin.addCases (loopHeads C base C) (fun _ : Fin 1=>1))
      (Fin.addCases (loopData B C R base source atoms left accumulator C)
        (fun _ : Fin 1=>CompareMachine.word C)) :=
  PhysicalRepeatStep.run SubstitutionBit.machine C (iterationBudget R)
    (loopHeads C base) (loopData B C R base source atoms left accumulator)
    (iteration B C R base source atoms left accumulator hlen hR hAtoms hstates)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
