
(* 1. Define an inductive data type myOdd: nat -> Set,
 so that you can prove the following lemma: 
 forall n, myOdd n -> exists m, n = 2*m +1 *)


Inductive myOdd : nat -> Set :=
| m_1 : myOdd 1
| m_IH : forall n : nat, myOdd n -> myOdd (S (S n)).

Check myOdd.

Lemma myOdd_lemma : forall n,
  myOdd n -> (exists m, n = 2*m + 1).
Proof.
  intros n.
  intros H.
  induction n as [| n'].
    exists 0. simpl. inversion H.
    induction H as [| ].
      exists 0. simpl. reflexivity.
      inversion IHmyOdd.
      exists (x + 1).
      assert (HH : n = 2 * x + 1 -> S (S n) = 2 * (x + 1) + 1).
        admit.
      apply HH.
      apply H0.
Qed.
     
      


(* 2. Define myOdd2 and myEven2 mutually inductively. 
Prove the lemma: forall n, myOdd2 n -> exists m, n = 2*m +1. *)