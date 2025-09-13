From  Require Import 1_goal 1_proof_auto 1_proof_manual.

Module VC_Correctness : VC_Correct.
  Include 1_proof_auto.
  Include 1_proof_manual.
End VC_Correctness.
