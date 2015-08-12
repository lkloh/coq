
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

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

Theorem plus_n_Sm : forall n m : nat, 
  n + (S m) = S (n + m).
Proof.
  admit.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  simpl. rewrite -> plus_0_r. reflexivity.
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.


Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  induction n as [| n'].
  simpl. reflexivity.
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Lemma expand_S : forall n : nat,
  S n = n + 1.
Proof.
    intros n.
    induction n.
    reflexivity.
    simpl. rewrite <- IHn. reflexivity.
Qed.

Lemma plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.
 

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
      rewrite -> expand_S.
      rewrite -> expand_S.
      rewrite -> H0.
      assert (HH : 2 * (x + 1) = 2 * x + 2).
        simpl.
        rewrite -> plus_0_r.
        simpl.
        destruct x.
        simpl. reflexivity.
      rewrite -> plus_0_r.
      rewrite -> plus_swap.
      rewrite <- plus_assoc.
      assert (two : 2 = 1 + 1). reflexivity.
      rewrite <- two.
      rewrite <- plus_assoc.
      reflexivity.
      rewrite <- plus_assoc.
      assert (two : 2 = 1 + 1). reflexivity.
      rewrite <- two.
      rewrite -> HH.
      rewrite <- plus_assoc.
      simpl.
      assert (three : 3 = 2 + 1). reflexivity.
      rewrite -> three.
      rewrite -> plus_assoc.
      reflexivity.
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

Example myOdd2_test_1: myOdd2 1.
Proof. apply o2_1. Qed.

Example myOdd2_test_2: myOdd2 5.
Proof. apply o2_IH. apply e2_IH. apply o2_IH. apply e2_IH. apply o2_1. Qed.

Example myEven2_test_3: myEven2 4.
Proof. apply e2_IH. apply o2_IH. apply e2_IH. apply o2_1. Qed.

Scheme myOdd2_mut := Induction for myOdd2 Sort Prop
  with myEven2_mut := Induction for myEven2 Sort Prop.
Check myOdd2_mut.

Lemma myOdd2_easier : forall n,
  myOdd2 n -> ble_nat 1 n = true.
Proof.
  apply (myOdd2_mut
    (fun n : nat => (fun mo => ble_nat 1 n = true))
    (fun n : nat => (fun me => ble_nat 0 n = true))
  ).
  reflexivity.
  intros. reflexivity.
  intros. reflexivity.
Qed.

Lemma Smn__m_Sn : forall n m,
  S (m + n) = m + S n.
Proof.
  intros n.
  induction n as [| n'].
  intros.
    rewrite -> plus_0_r.
    apply expand_S.
  intros.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.
    

Lemma myOdd2_lemma : forall n,
  myOdd2 n -> (exists m, n = 2*m + 1).
Proof.
  apply (myOdd2_mut
    (fun n : nat => (fun mo => exists m, n = 2*m + 1))
    (fun n : nat => (fun me => exists m, S n = 2*m + 1))
  ).
  exists 0.
    reflexivity.
  intros.
    apply H.
  intros. 
    inversion H.
    exists (S x).
    rewrite -> H0.
    simpl.
    apply f_equal.
    rewrite -> plus_0_r.
    rewrite <- plus_assoc.
    rewrite <- plus_n_Sm.
    rewrite -> plus_0_r.
    rewrite -> Smn__m_Sn.
    rewrite -> expand_S.
    rewrite -> plus_assoc.
    reflexivity.
Qed.



Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.


(* simpler example test *)

Inductive even: nat -> Prop :=
| even_base: even 0
| even_succ: forall n, odd n -> even (S n)
with odd: nat -> Prop :=
| odd_succ: forall n, even n -> odd (S n).

Scheme even_ind_2 := Minimality for even Sort Prop
with odd_ind_2 := Minimality for odd Sort Prop.

Check even_ind_2.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Lemma even_pos: forall n,
  even n -> ble_nat 0 n = true.
Proof.
  apply (even_ind_2
    (fun n =>  ble_nat 0 n = true)
    (fun n =>  ble_nat 1 n = true)
  ).
  reflexivity.
  intros. reflexivity.
  intros. reflexivity.
Qed.
  

  
      
      
      

      
      
      

    
  



