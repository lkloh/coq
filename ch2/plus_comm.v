Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  (* Case "n = 0" *)
  reflexivity.
  (* Case "n = S n'"*)
  simpl.
  rewrite-> IHn'.
  reflexivity.
Qed.

Theorem plus_r_0 : forall n:nat, 0 + n = n.
Proof.
  intros n.
  induction n as [| n'].
  (* Case "n = 0" *)
  reflexivity.
  (* Case "n = S n' *)
  simpl.
  rewrite <- IHn'.
  reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  (* case n=0 *)
  induction m as [| m'].
  (* subcase m=0 *)
  simpl.
  reflexivity.
  (* subcase m=S m' *)
  simpl.
  rewrite <- IHm'.
  (* case n= S n' *)
  simpl.
  reflexivity.
Qed.

