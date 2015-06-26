Theorem plus_O_n : forall n : nat, O + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_1 : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_1 : forall n:nat, O * n = O.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example: forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.


Theorem plus_id_exercise : forall n m O : nat,
  n = m -> m = O -> n + m = m + O.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  intros H2.
  rewrite <- H2.
  reflexivity.Qed.

  

Theorem plus_id_exercise : ∀n m o : nat,
  n = m → m = o → n + m = m + o.
Proof.
  intros n m o.
  intros H.
  rewrite -> H.
  reflexivity.
  Qed.




