Theorem andb_true_elim1 : forall (b c : bool),
  (andb b c = true) -> (b = true).
Proof.
  intros b c H.
  destruct b.
  reflexivity.
    rewrite <- H.
    reflexivity.
  Qed.

