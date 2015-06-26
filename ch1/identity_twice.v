Theorem identity_fn_applied_twice : forall (f : bool -> bool), 
  (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.


Theorem negation_twice : forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  destruct b as [|].
  reflexivity.
  reflexivity.
Qed.


  

