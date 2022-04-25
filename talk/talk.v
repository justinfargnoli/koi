Inductive Natural : Set :=
  | Zero : Natural
  | Successor (n : Natural) : Natural.

Fixpoint add a b := match a with
    | Zero => b
    | Successor n => 
        Successor (add n b)
    end.

Theorem plus_identity : forall a b : Natural, 
  a = b -> (add a a = add b b).
Proof.
  intros a b H.
  rewrite -> H.
  reflexivity.
Qed.

Definition plus_identity_elaborated : 
  forall a b : Natural, a = b -> add a a = add b b := 
  fun (a b : Natural) (H : a = b) =>
    eq_ind_r 
      (fun a0 : Natural => add a0 a0 = add b b) 
      eq_refl H.




























      








(* addition examples *)

(* add `a` and `b`*)
(* Inductive Natural : Set :=
  | Zero : Natural
  | Successor (n : Natural) : Natural.

Fixpoint add (a b : Natural) :=
  match a with
  | Zero => b
  | Successor (n : Natural) => 
      Successor (add n b).

Fixpoint add :=
  fun (a : Natural) => 
    fun (b : Natural) =>
      match a with
      | Zero => b
      | Successor (n : Natural) => 
          Successor (add n b).

Fixpoint add :=
  fun (a : Natural) => 
    fun (b : Natural) =>
      (* add `a` and `b`*). *)

(* Compute add Zero Zero. *) 

Compute Zero. (* 0 *)

Compute Successor Zero. (* 1 *)

Compute Successor (Successor (Successor Zero)). (* 3 *)

Definition natural_identity (natural : Natural) := 
  natural.


(* List *)

Inductive List (T : Set) : Set :=
| ListNil : List T
| ListCons (x : T) (l : List T) : List T.

Fixpoint list_append (T : Set) (n m : List T) : List T :=
  match n with
  | ListNil _ => m
  | ListCons _ x l => ListCons T x (list_append T l m)
  end.


Compute list_append nat (ListCons nat 0 (ListNil nat)) (ListCons nat 1 (ListNil nat)).


(* Vector *)

Inductive Vector (T : Set) : nat -> Set :=
| Nil : Vector T 0
| Cons (x : T) (length : nat) (v : Vector T length) 
    : Vector T (S length).

Compute Nil nat. (* [] *)

Compute Cons nat 0 0 (Nil nat). (* [ 0 ] *)

Compute Cons nat 1 1 (Cons nat 0 0 (Nil nat)). (* [ 0, 1 ] *)

Fixpoint append (T : Set) (n m : nat) 
      (a : Vector T n) (b : Vector T m) : Vector T (n + m) :=
  match a with
  | Nil _ => b
  | Cons _ x length v => 
        Cons T x (length + m) (append T length m v b)
  end.

(* Fixpoint append := 
  fun (T : Set) =>
    fun (n : nat) => 
      fun (m : nat) => 
        fun (a : Vector T n) => 
          fun (b : Vector T m) 
            (* append body *). *)

(* Fixpoint append (T : Set) (n m : nat) 
        (a : Vector T n) (b : Vector T m) 
        : Vector T (n + m) :=
  match a with
  | Nil _ => b
  | Cons _ x length v => 
      Cons T x (length + b) (append T length m v b)
  end. *)



(* Logic *)

Inductive True_ : Prop :=
| TrueConstruct : True_.

Inductive And (A B : Prop) : Prop :=
| AndConstruct (a : A) (b : B) : And A B.

Compute AndConstruct True_ True_ TrueConstruct TrueConstruct. (* True && True *)


Inductive False_ : Prop.

Inductive Or (A B : Prop) : Prop :=
| OrLeft (a : A) : Or A B
| OrRight (b : B) : Or A B.

Compute OrLeft True_ False_ TrueConstruct. (* True || False *)


(* modus ponens*)

Definition modus_ponens 
      (P Q : Prop) 
      (implication : P -> Q) 
      (p : P) 
      : Q := 
      implication p.

