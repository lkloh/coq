Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  case "b = true". (* <----- here *)
    reflexivity.
  case "b = false". (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.
