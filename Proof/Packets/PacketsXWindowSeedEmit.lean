import Proof.Packets.PacketsXWindowSeedLayout
import Proof.Packets.PacketsXDescendingWindowMeaning

/-! Complete actual window provider core: cold/reentry seeding followed by
both checked descending runtime enumeration loops. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def emit := TapeEmbedding.machine 7 DescendingWindowLoop.machine
def complete := Composition.machine machine emit
def completeBudget (R v u M W : Nat) := budget R v u M W+1+DescendingWindowLoop.budget u (2*W) R

theorem emit_run (R v u M offset W target : Nat)
    (hfit : offset+2*W<2^u) (hd : 2*W+1<2^u) (ht : target<2^u) (hscalar : 2*u≤R)
    (hMv : M≤2^v) (hmeta : 2*v+2*W+3≤R)
    (hC : ∀k≤2*W,CloseoutRowsModeElementary.budget v k M+1≤R) :
    Step emit (DescendingWindowLoop.budget u (2*W) R)
      (H 1) (produced R v u M offset W target)
      (afterHeads v M offset target (2*W+1)) (after R v u M offset W target (2*W+1)) := by
  have h:=((DescendingWindowLoop.run v u M offset target (2*W) R 0 false false []
    hfit hd ht hscalar hMv hmeta hC).pad (loopCaps R)).embed
    (fun _ : Fin 7=>0) (metadata R v u M offset W target)
  rw [produced_layout R v u M offset W target (by omega),produced_heads]
  exact h

theorem complete_run (R v u M offset W target d : Nat) (A : Fin 69→List Bool)
    (hdriver : d≤1) (hu : 2*u+1≤R) (hv : 2*v+1≤R) (hM : M+1≤R) (hMv : M≤2^v)
    (hraw : A 50=List.replicate R true) (hlog : A 51=List.replicate (R+3) false)
    (hmasters : ∀j : Fin 7,A (Fin.natAdd 62 j)=metadata R v u M offset W target j)
    (hprivate : ∀j,(A (privateSlot j)).length≤R)
    (hfit : offset+2*W<2^u) (hd : 2*W+1<2^u) (ht : target<2^u)
    (hmeta : 2*v+2*W+3≤R)
    (hC : ∀k≤2*W,CloseoutRowsModeElementary.budget v k M+1≤R) :
    Step complete (completeBudget R v u M W) (H d) A
      (afterHeads v M offset target (2*W+1)) (after R v u M offset W target (2*W+1)) :=
  (run R v u M offset W target d A hdriver hu hv hM hMv hraw hlog hmasters hprivate).seq
    (emit_run R v u M offset W target hfit hd ht (by omega) hMv hmeta hC)

theorem emitted_word (v M offset W target : Nat) :
    emitted v M offset W target=
      (WindowNativeOrder.positionalWindow v M offset (2*W) target).flatMap ExtIncidence.monomialWord := by
  simpa only [emitted,List.nil_append] using
    DescendingWindowMeaning.output_word v M offset target (2*W) []

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
