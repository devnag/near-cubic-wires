import Proof.Packets.SubstitutionOuterScan
import Proof.Packets.SubstitutionOuterAccumulate
import Proof.Packets.SubstitutionOuterReload

/-! One complete executed monomial step of the frozen substitution: consume
all code bits in reverse, accumulate the product on the left, restore one,
and physically reload the code counter for the next monomial. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def productState (C base : Nat) (source : List Bool) (atoms : List Packet) (left : Packet) :=
  SubstitutionScan.scan C base source atoms left (one C) C

def InnerGuard (C R base : Nat) (source : List Bool) (atoms : List Packet) (left : Packet) : Prop :=
  ∀ k,k<C→
    let p:=SubstitutionScan.scan C base source atoms left (one C) k
    let selected:=atoms.getD (C-(k+1)) []
    PacketVector.Fits R p.1 ∧ (∀ bits∈p.2,bits.length=C) ∧
    (∀ i,(ReusableArithmetic.data C selected p.2 i).length≤R) ∧
    NormalizedMultiply.budget C selected p.2+3≤R

structure Guard (C R base : Nat) (source : List Bool) (atoms : List Packet) (left stored : Packet) : Prop where
  inner : InnerGuard C R base source atoms left
  leftFits : VectorAccumulator.Fits R (productState C base source atoms left).1
  productFits : VectorAccumulator.Fits R (productState C base source atoms left).2
  storedFits : VectorAccumulator.Fits R stored
  productWidth : ∀ bits∈(productState C base source atoms left).2,bits.length=C
  storedWidth : ∀ bits∈stored,bits.length=C
  addInput : ∀ i,(ReusableArithmetic.data C (productState C base source atoms left).2 stored i).length≤R
  addFuel : NormalizedAddition.budget C (productState C base source atoms left).2 stored+3≤R

noncomputable def body := Composition.machine scanMachine (Composition.machine accumulate reload)
def bodyBudget (C R : Nat) := 200*(C+1)*(R+1)^2

theorem one_fits (C R : Nat) (hC : C+2≤R) : VectorAccumulator.Fits R (one C) := by
  constructor
  · simpa [one] using (show C≤R by omega)
  · simpa [one] using (show 2≤R by omega)

theorem body_run (C R base : Nat) (source : List Bool) (atoms : List Packet) (left stored : Packet)
    (hlen : atoms.length=C) (hC : C+2≤R)
    (hAtoms : ∀ P∈atoms,PacketVector.Fits R P ∧ ∀ bits∈P,bits.length=C)
    (guard : Guard C R base source atoms left stored) :
    let product:=(productState C base source atoms left).2
    Step body (bodyBudget C R)
      (H (base+C) 1) (A C R C left (one C) (PacketVector.bank R atoms) source stored)
      (H base 1) (A C R C product (one C) (PacketVector.bank R atoms) source
        (VectorAccumulator.answer product stored)) := by
  dsimp only
  let p:=productState C base source atoms left
  have first:=dock_scan C R base source atoms left (one C) stored hlen (by omega) hAtoms guard.inner
  have second:=accumulate_run C R 0 base p.1 p.2 stored (PacketVector.bank R atoms) source
    guard.leftFits guard.productFits guard.storedFits (one_fits C R hC)
    guard.productWidth guard.storedWidth guard.addInput guard.addFuel
  have third:=reload_run C R 0 base p.2 (one C) (PacketVector.bank R atoms) source
    (VectorAccumulator.answer p.2 stored) hC (by omega)
  have result:=first.seq (second.seq third)
  apply result.enlarge
  have addBound:=accumulate_bound C R p.2 stored (by have h:=guard.addFuel;change NormalizedAddition.budget C p.2 stored+3≤R at h;omega)
  unfold SubstitutionScan.budget SubstitutionScan.iterationBudget bodyBudget
  nlinarith [Nat.zero_le C,Nat.zero_le R]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
