
(* 1. Define an inductive data type myOdd: nat -> Set,
 so that you can prove the following lemma: 
 forall n, myOdd n -> exists m, n = 2*m +1 *)



Goal
  exists x, 1 + x = 3.
Proof.                        (* ⊢ exists x, 1 + x = 3 *)
  eapply ex_intro.            (* ⊢ 1 + ?42 = 3 *)
  simpl.                      (* ⊢ S ?42 = 3 *)
  apply f_equal.              (* ⊢ ?42 = 2 *)
  reflexivity.                (* proof completed *)
Qed.

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
  eapply ex_intro.

(* 2. Define myOdd2 and myEven2 mutually inductively. 
Prove the lemma: forall n, myOdd2 n -> exists m, n = 2*m +1. *)