Inductive Natural : Set :=
  | Zero : Natural
  | Successor (n : Natural) : Natural.

Fixpoint add a b := match a with
    | Zero => b
    | Successor n => 
        Successor (add n b)
    end.

Theorem plus_identity : forall n m : Natural, 
  n = m -> (add n n = add m m).
Proof.
  intros n m H.
  rewrite -> H.
  reflexivity.
Qed.

Print plus_identity.

Definition plus_identity_elaborated : 
  forall n m : Natural, n = m -> add n n = add m m := 
  
  fun (n m : Natural) (H : n = m) =>
    eq_ind_r 
      (fun n0 : Natural => add n0 n0 = add m m) 
      eq_refl H.

























(* add `a` and `b`*)

(* Definition add (a b : Natural) :=
  match a with
  | Zero => b
  | Successor (n : Natural) => Successor (add n b).

Compute add Zero Zero. *)

Compute Zero. (* 0 *)

Compute Successor Zero. (* 1 *)

Compute Successor (Successor (Successor Zero)). (* 3 *)

Definition natural_identity (natural : Natural) := 
  natural.



Inductive List (T : Set) : Set :=
| Nil : List
| Cons (x : T) (l : List T) : List.



Inductive Vector (T : Set) : Natural -> Set :=
| Nil : Vector T Zero
| Cons (x : T) 
    (length : Natural) 
    (v : Vector T length) 
    : Vector T (Successor length).

Compute Nil Natural. (* [] *)

Compute Cons Natural (Successor Zero) Zero (Nil Natural). (* [ 1 ] *)

Compute Cons Natural Zero (Successor Zero) 
  (Cons Natural (Successor Zero) Zero (Nil Natural)). (* [ 0, 1 ] *)


Fixpoint add (a b : Natural) : Natural :=
  match a with
  | Zero => b
  | Successor x => Successor (add x b)
  end.


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