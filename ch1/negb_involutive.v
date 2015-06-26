Theorem negb_involutive : forall b : bool,
negb (negb b) = b.

Proof.
  intros b.
  destruct b as [|].
    reflexivity.
    reflexivity.
Qed.



