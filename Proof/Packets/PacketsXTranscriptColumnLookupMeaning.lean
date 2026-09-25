import Proof.Packets.PacketsXTranscriptColumnLookupStep

/-! Literal ordered list identities for one-hot lookup; rejected candidates
remain present as zero terms and are never removed or permuted. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumnLookupMeaning
open NearCubicWires.CanonicalFourfoldRowProgram
abbrev Poly := Ring.Poly Nat

def term (P : Poly) (bit : Bool) : Poly := if bit then P else []

end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumnLookupMeaning
