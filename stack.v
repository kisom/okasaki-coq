(* 
The first data type defined in chapter 2 of PFDS.

Its signature is defined as (in SML):

signature STACK = 
sig
  type a Stack
  
  val empty       :: a Stack
  val isEmpty     :: a Stack -> bool

  val cons        :: a x a Stack -> a Stack
  val head        :: a Stack -> a
  val tail        :: a Stack -> a Stack
end

*)

Require Import Bool.

Inductive stack (T:Set) : Set :=
  | Empty : stack T
  | Cons : T -> stack T -> stack T.

Definition isEmpty T (s : stack T) : bool :=
  match s with
    | Empty => true
    | _ => false
  end.

Definition head T (s : stack T) : option T :=
  match s with
    | Empty => None
    | Cons s' _ => Some s'
  end.

Definition tail T (s : stack T) : stack T :=
  match s with
    | Empty => Empty T
    | Cons _ s' => s'
  end.

(* Example of empty list. *)
Eval simpl in Empty nat.
Eval simpl in isEmpty nat (Empty nat).

(* Example of a list of size 1. *)
Eval simpl in Cons nat 1 (Empty nat).
Eval simpl in isEmpty nat (Cons nat 1 (Empty nat)).

Definition list1 := Cons nat 1 (Empty nat).
Definition list2 := Cons nat 2 list1.

Eval simpl in head nat list1.
Eval simpl in head nat list2.
Eval simpl in tail nat list1.
Eval simpl in tail nat list2.
Eval simpl in head nat (tail nat list2).
