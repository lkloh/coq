Module Church.

(** In this exercise, we will explore an alternative way of defining
    natural numbers, using the so-called _Church numerals_, named
    after mathematician Alonzo Church. We can represent a natural
    number [n] as a function that takes a function [f] as a parameter
    and returns [f] iterated [n] times. More formally, *)

Definition nat := forall X : Type, (X -> X) -> X -> X.

(** Let's see how to write some numbers with this notation. Any
    function [f] iterated once shouldn't change. Thus, *)

Definition one : nat := 
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** [two] should apply [f] twice to its argument: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** [zero] is somewhat trickier: how can we apply a function zero
    times? The answer is simple: just leave the argument untouched. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] will be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f]. Notice in particular
    how the [doit3times] function we've defined previously is actually
    just the representation of [3]. *)

Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
  f (f (f n)).

Definition three : nat := @doit3times.

(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)    

(** Successor of a natural number *)

Definition succ (n : nat) : nat :=
  fun {X:Type} (f:X -> X) (n: X) => f n.

Example succ_1 : succ zero = one.
admit.

Example succ_2 : succ one = two.
admit.

Example succ_3 : succ two = three.
Proof. (* FILL IN HERE *) Admitted.

(** Addition of two natural numbers *)

Definition plus (n m : nat) : nat :=
  match n with
    | zero => m
    | succ n' => match m with
                   | zero => n
                   | succ m' => succ (succ (plus n' m'))
                 end
end.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* FILL IN HERE *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* FILL IN HERE *) Admitted.

(** Multiplication *)

Definition mult (n m : nat) : nat := 
  (* FILL IN HERE *) admit.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* FILL IN HERE *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* FILL IN HERE *) Admitted.

(** Exponentiation *)

(** Hint: Polymorphism plays a crucial role here. However, choosing
    the right type to iterate over can be tricky. If you hit a
    "Universe inconsistency" error, try iterating over a different
    type: [nat] itself is usually problematic. *)

Definition exp (n m : nat) : nat :=
  (* FILL IN HERE *) admit.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. (* FILL IN HERE *) Admitted.

Example exp_3 : exp three zero = one.
Proof. (* FILL IN HERE *) Admitted.

End Church.
