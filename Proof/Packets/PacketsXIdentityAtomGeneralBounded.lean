import Proof.Packets.PacketsXIdentityAtomBounded

/-! The final occurrence-to-pool table uses arbitrary raw source atom pairs.
All copy, native parsing, normalization and whole-cache space guards follow
from the actual raw count, degree and index bounds. No singleton restriction
is imposed on these atoms. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomGeneralBounded
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair word cacheWord)
open Theorem25Completion.CycleBounds

theorem pair_length (C : Nat) (p : Pair)
    (hf : ∀m∈p.1++p.2,∀i∈m,i<C) (hd : ∀m∈p.1++p.2,m.length≤C) :
    (word p).length≤4*(p.1++p.2).length*(C+1)^2+2 := by
  have hl := (native_stream_length C p.1).trans
    (native_parser_cost C p.1 (fun m hm=>hf m (List.mem_append_left _ hm))
      (fun m hm=>hd m (List.mem_append_left _ hm)))
  have hr := (native_stream_length C p.2).trans
    (native_parser_cost C p.2 (fun m hm=>hf m (List.mem_append_right _ hm))
      (fun m hm=>hd m (List.mem_append_right _ hm)))
  unfold word
  simp only [List.length_append]
  nlinarith only [hl,hr]

theorem small_polynomials (C N : Nat) :
    C*(4*N*(C+1)^2+2)≤8192*(N+1)^3*(C+1)^3 ∧
    32*(4*N*(C+1)^2+4)≤8192*(N+1)^3*(C+1)^3 := by
  have hn : N≤(N+1)^3 := (by omega : N≤N+1).trans (Nat.le_self_pow (by decide) _)
  have hn1 : 1≤(N+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hc : (C+1)^2≤(C+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp := Nat.mul_le_mul hn (le_refl ((C+1)^3))
  have hs := Nat.mul_le_mul hn hc
  have ht := Nat.mul_le_mul hn1 (by nlinarith [Nat.zero_le (C^2)] : C+1≤(C+1)^3)
  constructor
  · nlinarith only [hp,ht,Nat.zero_le (N*(C+1)^2)]
  · nlinarith only [hs,ht,Nat.zero_le C]

theorem resources (C w : Nat) (cs : List Pair) (hcs : cs.length≤C)
    (hc : ∀p∈cs,(p.1++p.2).length≤2^(2*w))
    (hf : ∀p∈cs,∀m∈p.1++p.2,∀i∈m,i<C)
    (hd : ∀p∈cs,∀m∈p.1++p.2,m.length≤C) :
    (cacheWord cs).length≤commonReserve C w ∧
    ∀p∈cs,CloseoutRowsRawPairCopy.budget p≤commonReserve C w+3 := by
  have hb := packet_reserve_bound C w (2^(2*w)) (le_refl _)
  have hp := small_polynomials C (2^(2*w))
  have hw (p : Pair) (hm : p∈cs) : (word p).length≤4*2^(2*w)*(C+1)^2+2 := by
    have h:=pair_length C p (hf p hm) (hd p hm)
    have ht:=Nat.mul_le_mul_right ((C+1)^2) (Nat.mul_le_mul_left 4 (hc p hm))
    omega
  constructor
  · have hs : (cacheWord cs).length≤cs.length*(4*2^(2*w)*(C+1)^2+2) := by
      simpa only [cacheWord,List.length_flatMap] using
        sum_map_bound cs (fun p=>(word p).length) (4*2^(2*w)*(C+1)^2+2) hw
    exact hs.trans ((Nat.mul_le_mul_right _ hcs).trans (hp.1.trans hb))
  · intro p hm
    have h:=CloseoutRowsRawPairCopy.budget_bound p
    have hn:=Nat.mul_le_mul_left 32 (by have ht:=hw p hm;omega : (word p).length+2≤4*2^(2*w)*(C+1)^2+4)
    exact (h.trans (hn.trans (hp.2.trans hb))).trans (by omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomGeneralBounded
