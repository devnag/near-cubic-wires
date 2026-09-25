import Proof.Rows.MaskProductRow

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

abbrev last := TapeEmbedding.machine 1 PhysicalSupportReturn.machine
abbrev machine := Composition.machine raw last

theorem embed_cfg {s : Nat} (q : Fin s) (B dh mh pos : Nat) (left right out count : List Bool) :
    TapeEmbedding.config (fun _ : Fin 1=>count.length) (fun _=>count)
      (PhysicalSupportReturn.cfg q B dh mh left right pos out)=
      cfg q B dh mh left right pos out count := by
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

theorem return5_run (B base pos : Nat) (left right out count : List Bool) :
    ∃ r,runFrom last (B+2) (cfg 0 B (B+1) (base+B) left right pos out count)=some r ∧
      r.final=cfg 2 B 1 base left right pos out count ∧ r.steps=B+2 := by
  obtain ⟨r,hr,hf,hs⟩:=return_run B base pos left right out
  have h:=TapeEmbedding.run_embed PhysicalSupportReturn.machine
    (fun _ : Fin 1=>count.length) (fun _=>count) _ _ r hr
  rw [embed_cfg] at h
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>count.length) (fun _=>count) r,h,?_,hs⟩
  change TapeEmbedding.config _ _ r.final=_
  rw [hf,embed_cfg]

theorem pairs_run (pairs : List (Bool×Bool)) (mpre mtail pre tail out count : List Bool) :
    ∃ r,runFrom machine (3*pairs.length+6)
      (cfg machine.start pairs.length 1 mpre.length (mpre++pairs.map Prod.fst++mtail)
        (pre++pairs.map Prod.snd++tail) pre.length out count)=some r ∧
      r.final=cfg 7 pairs.length 1 mpre.length
        (mpre++pairs.map Prod.fst++mtail) (pre++pairs.map Prod.snd++tail)
        (pre.length+pairs.length) (out++frame (values pairs)++[false,false]) (count++[true]) ∧
      r.steps=3*pairs.length+6 := by
  obtain ⟨first,hr,hf,hs⟩:=raw_pairs_run pairs mpre mtail pre tail out count
  obtain ⟨second,sr,sf,ss⟩:=return5_run pairs.length mpre.length (pre.length+pairs.length)
    (mpre++pairs.map Prod.fst++mtail) (pre++pairs.map Prod.snd++tail)
    (out++frame (values pairs)++[false,false]) (count++[true])
  have join : Composition.restart first.final last.start=
      cfg 0 pairs.length (pairs.length+1) (mpre.length+pairs.length)
        (mpre++pairs.map Prod.fst++mtail) (pre++pairs.map Prod.snd++tail)
        (pre.length+pairs.length) (out++frame (values pairs)++[false,false]) (count++[true]) := by
    rw [hf];rfl
  rw [←join] at sr
  have h:=Composition.run_join raw last _ _ _ first second hr sr
  have fuel : (2*pairs.length+3)+1+(pairs.length+2)=3*pairs.length+6 := by omega
  rw [fuel] at h
  refine ⟨Composition.joinedReceipt first second,h,?_,?_⟩
  · change Composition.rightConfig 5 second.final=_
    rw [sf]
    rfl
  · change first.steps+1+second.steps=_
    omega

/-- Both complete source banks are retained, including arbitrary prefixes
and suffixes. The returned left cursor is exactly its original row base. -/
theorem row_run (mask bits mpre mtail pre tail out count : List Bool)
    (width : mask.length=bits.length) :
    ∃ r,runFrom machine (3*bits.length+6)
      (cfg machine.start bits.length 1 mpre.length (mpre++mask++mtail)
        (pre++bits++tail) pre.length out count)=some r ∧
      r.final=cfg 7 bits.length 1 mpre.length (mpre++mask++mtail)
        (pre++bits++tail) (pre.length+bits.length)
        (out++frame (values (mask.zip bits))++[false,false]) (count++[true]) ∧
      r.steps=3*bits.length+6 := by
  obtain ⟨r,hr,hf,hs⟩:=pairs_run (mask.zip bits) mpre mtail pre tail out count
  have hm:=List.map_fst_zip (l₁:=mask) (l₂:=bits) width.le
  have hb:=List.map_snd_zip (l₁:=mask) (l₂:=bits) width.ge
  have hl : (mask.zip bits).length=bits.length := by simp [width]
  rw [hm,hb,hl] at hr hf
  rw [hl] at hs
  exact ⟨r,hr,hf,hs⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
