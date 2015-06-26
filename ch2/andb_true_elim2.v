Require Export Basics.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Theorem andb_true_elim2 : forall (b c : bool),
  (andb b c = true) -> (c = true).
Proof.
  intros b c H.
  destruct c.
  (* case c = true *)
  reflexivity.
  (* case c = false *)
  rewrite <- H.
  simpl.
  destruct b.
  (* subcase b = true *)
  reflexivity.
  (* subcase b = false *)
  reflexivity.
Qed. 
  