Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  (* Case "n = 0". *)
  reflexivity.
  (* Case "n = S n'". *)
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.