Theorem succ_def : forall n : nat,
 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.



Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H. 
  rewrite -> succ_def.
  rewrite -> H.
  reflexivity.
Qed.





