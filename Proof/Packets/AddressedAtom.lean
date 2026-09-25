import Proof.Packets.DenseAtomInitialize
import Proof.Packets.AddressedAtomMaterialize

/-! First dense atom pass: actual zero-table allocation followed by the
complete resident-cache materializer. All entries begin as physically
written zero packets; no dense bank is supplied at entry. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open AddressedAtomMaterialize (H A)
open AddressedAtomProgram (table codes)
noncomputable def boot :=  TapeEmbedding.machine 1 DenseAtomInitialize.machine
noncomputable def machine := Composition.machine boot AddressedAtomMaterialize.machine
def budget (C R count : Nat) := DenseAtomInitialize.budget C R+1+AddressedAtomMaterialize.budget C R count

theorem run (C R : Nat) (coding : Nat→Nat) (cs : List Pair)
    (hR : C+2≤R) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,coding i<C)
    (hcache : (cacheWord cs).length≤R) (hcodeword : (codes coding cs).length≤R)
    (hcopy : ∀p∈cs,CloseoutRowsRawPairCopy.budget p≤R+3)
    (hfits : ∀p∈cs,∀m∈p.1++p.2,∀i∈m,i<C)
    (hdata : ∀p∈cs,∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤R)
    (hfuel : ∀p∈cs,NativeNormalized.budget C (p.1++p.2)+3≤R) :
    Step machine (budget C R cs.length) (H 0) (A C R coding cs [] 0)
      (H 0) (A C R coding cs (table C coding cs (List.replicate C []) cs.length) 0) := by
  have init := (DenseAtomInitialize.run C R 0 (cacheWord cs) (codes coding cs) hR).embed
    (fun _ : Fin 1=>1) (fun _=>ZeroPadding.pad R (CompareMachine.word cs.length))
  have init' : Step boot (DenseAtomInitialize.budget C R)
      (H 0) (A C R coding cs [] 0) (H 0) (A C R coding cs (List.replicate C []) 0) := by
    convert init using 1 <;> rfl
  exact init'.seq (AddressedAtomMaterialize.run C R coding cs (List.replicate C []) hR hcount hcodes
    hcache hcodeword (by simp) (by intro P hP; have hp : P=[] := List.mem_replicate.mp hP |>.2; subst P; exact PacketVector.empty_fits R (by omega)) hcopy hfits hdata hfuel)

end PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomCold
