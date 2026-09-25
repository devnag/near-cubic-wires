import Proof.Packets.NativeAtomClear

/-! One closed reusable dense-atom transaction: copy the resident raw atom
pair, parse and normalize it, read its actual singleton code, overwrite the
selected dense entry, and reset operand/index work for the next atom. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair word)

def answer (C : Nat) (p : Pair) := NormalizerOrder.ordered (NativeNormalized.masks C (p.1++p.2))
def updatedBank (C R : Nat) (p : Pair) (pre post : List Bool) :=
  pre++ZeroPadding.pad R (answer C p).flatten++
    ZeroPadding.pad R (CompareMachine.word (answer C p).length)++post
noncomputable def transaction := Composition.machine (TapeEmbedding.machine 4 NativePairNormalize.machine)
  (Composition.machine parse (Composition.machine store cleanup))
def transactionBudget (C R code : Nat) (p : Pair) := NativePairNormalize.budget C R p+1+
  ((2*code+9)+1+((PacketBank.lookupBudget R code+4)+1+(2*R+6)))

theorem transaction_run (C R code : Nat) (pairPre pairPost codePre codePost bankPre oldPayload oldCount bankPost : List Bool)
    (p : Pair) (hC : C≤R) (hR : 1≤R) (hcopy : CloseoutRowsRawPairCopy.budget p≤R+3)
    (hfits : ∀m∈p.1++p.2,∀i∈m,i<C)
    (hdata : ∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤R)
    (hfuel : NativeNormalized.budget C (p.1++p.2)+3≤R)
    (hpre : bankPre.length=2*code*R) (hop : oldPayload.length=R) (hoc : oldCount.length=R)
    (hp : (answer C p).flatten.length≤R) (hc : (answer C p).length+1≤R) (hi : code+1≤R) :
    Step transaction (transactionBudget C R code p)
      (heads pairPre.length codePre.length 0)
      (data C R (pairPre++word p++pairPost) (codePre++NativeLiteralCode.word code++codePost)
        (bankPre++oldPayload++oldCount++bankPost) [] 0)
      (heads (pairPre.length+(word p).length) (codePre.length+code+6) 0)
      (data C R (pairPre++word p++pairPost) (codePre++NativeLiteralCode.word code++codePost)
        (updatedBank C R p bankPre bankPost) [] 0) := by
  let pairs:=pairPre++word p++pairPost
  let codes:=codePre++NativeLiteralCode.word code++codePost
  let before:=bankPre++oldPayload++oldCount++bankPost
  let pairPos:=pairPre.length+(word p).length
  have first:=(NativePairNormalize.run C R pairPre pairPost p hC hR hcopy hfits hdata hfuel).embed
    (![codePre.length,0,0,0] : Fin 4→Nat)
    (![codes,ZeroPadding.pad R (CompareMachine.word 0),before,List.replicate R false] : Fin 4→List Bool)
  have first' : Step (TapeEmbedding.machine 4 NativePairNormalize.machine) (NativePairNormalize.budget C R p)
      (heads pairPre.length codePre.length 0) (data C R pairs codes before [] 0)
      (heads pairPos codePre.length 0) (data C R pairs codes before (answer C p) 0) := by
    apply first.congr_in rfl
    funext i
    fin_cases i <;>rfl
  have second:=parse_run C R pairPos code pairs codePre codePost before (answer C p) hR
  have third:=store_run C R pairPos (codePre.length+code+6) code pairs codes
    bankPre oldPayload oldCount bankPost (answer C p) hpre hp hc hop hoc
  have last:=cleanup_run C R pairPos (codePre.length+code+6) code pairs codes
    (updatedBank C R p bankPre bankPost) (answer C p) hp hc hi
  exact first'.seq (second.seq (third.seq last))

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
