
(* 1. Define an inductive data type myOdd: nat -> Set,
 so that you can prove the following lemma: 
 forall n, myOdd n -> exists m, n = 2*m +1 *)


Inductive myOdd : nat -> Set :=
| m_1 : myOdd 1
| m_IH : forall n : nat, myOdd n -> myOdd (S (S n)).

Check myOdd.

Lemma plus_0_r: forall r : nat,
  r + 0 = r.
Proof.
  intros r.
  induction r as [| r'].
  reflexivity.
  simpl. rewrite -> IHr'. reflexivity.
Qed.

Lemma n_eq_m__Sn_eq_Sm : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n.
  destruct n as [| n'].
    intros m H. rewrite <- H. reflexivity.
    intros m H. rewrite -> H. reflexivity.
Qed.

Lemma helper : forall (n x : nat),
  n = 2 * x + 1 -> S (S n) = 2 * (x + 1) + 1.
Proof.
  intros n.
  induction n as [| n'].
    intros x H. 
    destruct x.
      simpl in H. inversion H.
      inversion H.
    intros x H.
      destruct x.
      simpl in H. simpl. rewrite -> H. reflexivity.
      simpl. apply n_eq_m__Sn_eq_Sm.
      rewrite -> plus_0_r.
      simpl in H. rewrite -> plus_0_r in H. 
  

Lemma myOdd_lemma : forall n,
  myOdd n -> (exists m, n = 2*m + 1).
Proof.
  intros n.
  intros H.
  induction n as [| n'].
    inversion H.
    induction H as [| ].
      exists 0. reflexivity.
      inversion IHmyOdd.
      exists (x + 1).
      assert (HH : n = 2 * x + 1 -> S (S n) = 2 * (x + 1) + 1).
        admit.
      apply HH.
      apply H0.
Qed.



(* 2. Define myOdd2 and myEven2 mutually inductively. 
   Prove the lemma: forall n, myOdd2 n -> exists m, n = 2*m +1. *)

(*
  Inductive myEven2: nat -> Set :=
    | e2_1 : myEven2 0
    | e2_IH : forall n : nat, myOdd2 n -> myEven2 (S n)
  with myOdd2 : nat -> Set :=
    | o2_IH : forall n : nat, myEven2 n -> myOdd2 (S n).
*)

Inductive myOdd2: nat -> Set :=
  | o2_1 : myOdd2 1
  | o2_IH : forall n : nat, myEven2 n -> myOdd2 (S n)
with myEven2 : nat -> Set :=
  | e2_IH : forall n : nat, myOdd2 n -> myEven2 (S n).

  


Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

Lemma myOdd2_lemma : forall n,
  myOdd2 n -> (exists m, n = 2*m + 1).
Proof.
  intros n.
  induction n as  [| n'].
    intros H. inversion H.
    intros H.
      inversion H.
      exists 0. reflexivity.
      destruct H1.
      admit.

Lemma myOdd2_lemma' : forall n,
  myOdd2 n -> (exists m, n = 2*m + 1).
Proof.
  intros.
  induction n as [| n'].
    inversion H.
    inversion H. exists 0. reflexivity.
      assert (HH :  
     
      
      
      

      
      
      

    
  



