import Proof.Packets.PacketsXWindowLiteralProviderCost
import Proof.Packets.PacketsXWindowLiteralProviderLayout
import Proof.Packets.WindowLiteralNumeric
import Proof.Packets.PacketsXWindowElementaryGuard

/-! One actual per-child provider theorem at a uniform fuel. Its digit width
is computed from the alphabet length. All scalar and full-enumerator guards
follow from the concrete population and the degree census. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (cacheWord)
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

def uniformBudget (C w : Nat) := 2199023255552*(C+1)^6*2^(8*w)

theorem literal_provider_bounded (C w offset W target : Nat) (codes : List Nat)
    (hc : codes.Pairwise (·<·)) (hcodes : ∀c∈codes,c < C)
    (hsize : codes.length ≤ C) (hpositive : 1 ≤ codes.length) (hw : 3 ≤ w)
    (hW : W ≤ 64*(C+2)) (ho : offset ≤ 2*C) (ht : target ≤ 2*C)
    (hcount : (codes.length+1)^(2*W) ≤ 2^w)
    (left : List (List Bool)) (A : Fin 256→List Bool)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C (commonReserve C w) left [] i)
    (acache : A 186=ZeroPadding.pad (commonReserve C w) (cacheWord (literalPairs codes)))
    (hwork : ∀i,Workspace.selected i→(A i).length ≤ commonReserve C w)
    (hmeta : ∀j : Fin 7,A (seedPorts (j.natAdd 62))=
      WindowSeed.metadata (commonReserve C w) (Nat.log 2 codes.length+1) (C+9)
        codes.length offset W target j)
    (hprivate : ∀j,(A (seedPorts (WindowSeed.privateSlot j))).length ≤ commonReserve C w) :
    Step literalProvider (uniformBudget C w) heads A heads
      (literalProviderOutput C (commonReserve C w) (Nat.log 2 codes.length+1) (C+9)
        offset W target codes A) := by
  let v:=Nat.log 2 codes.length+1
  have digit:=digit_width_guards codes.length
  have hv : v ≤ C+1:=digit.2.1.trans (by omega)
  have width:=width_from_census codes.length (2*W) w hpositive hcount
  have degree : 2*W+1 ≤ 2^w:=by have h : w < 2^w := Nat.lt_two_pow_self;omega
  obtain ⟨hu,hvR,_hm,_hd,hfields,hfit,hdfit,htfit⟩:=
    window_metadata_guards C w v codes.length W offset target hv hsize hW ho ht
  have enum:=elementary_guard C v codes.length w (2*W) hv hsize width digit.2.2 hcount
  have actual:=literal_provider_run C w v (C+9) offset W target codes hc hcodes hsize
    digit.1 hw degree hcount left A hengine acache hwork hu hvR hmeta hprivate
    hfit hdfit htfit hfields enum
  exact actual.enlarge (literal_provider_budget C w v codes.length W offset target codes
    hc hcodes rfl hsize hv digit.1 hw hW degree hcount)

theorem emitted_private_guard (C w offset W target : Nat) (codes : List Nat)
    (hc : codes.Pairwise (·<·)) (hsize : codes.length ≤ C)
    (hpositive : 1 ≤ codes.length) (hcount : (codes.length+1)^(2*W) ≤ 2^w) :
    (WindowSeed.emitted (Nat.log 2 codes.length+1) codes.length offset W target).length ≤
      commonReserve C w := by
  have width:=width_from_census codes.length (2*W) w hpositive hcount
  have degree : 2*W+1 ≤ 2^w:=by have h : w < 2^w := Nat.lt_two_pow_self;omega
  have h:=positional_stream_guard C w codes hsize hc (Nat.log 2 codes.length+1)
    offset (2*W) target (digit_width_guards codes.length).1 degree hcount
  rw [WindowSeed.emitted_word]
  simp only [ExtIncidence.stream,List.length_append,List.length_singleton] at h
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
