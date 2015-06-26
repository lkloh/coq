Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  (* case n=0 *)
  simpl.
  reflexivity.
  (* case n = S n' *)
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

