Theorem plus_r_0 : forall n:nat, 0 + n = n.
Proof.
  intros n.
  induction n as [| n'].
  (* Case "n = 0" *)
  reflexivity.
  (* Case "n = S n'" *)
  simpl.
  rewrite <- IHn'.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n'].
  (* case n=0 *)
  induction m as [| m'].
  (* subcase m=0 *)
  simpl.
  reflexivity.
  (* subcase m= S m' *)
  simpl.
  rewrite <- plus_r_0.
  rewrite <- plus_r_0.
  reflexivity.
  (* case n = S n'*)
  induction m as [| m'].
  (* subcase m = 0 *)
  simpl.
  rewrite -> IHn'.
  (* subcase m = S m'*)
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn'.
  simpl.
reflexivity.
simpl.
rewrite -> IHm'.
Qed.

