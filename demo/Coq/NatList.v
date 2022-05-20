Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
  
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
  
Theorem nil_app : forall l : natlist,
  app nil l = l.
Proof. reflexivity. Qed.

Print nil_app.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | cons h t => t
  end.
  
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | cons h t => S (length t)
  end.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.
    
Print tl_length_pred.

Print eq_refl.

Theorem app_length : forall l1 l2 : natlist,
  length (app l1 l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.
    
Print app_length.

Module Test.

Inductive Natural : Set :=
| Zero : Natural
| Successor (n : Natural) : Natural.

Fixpoint natural_add (a b : Natural) : Natural :=
match a with
| Zero => b
| Successor n => Successor (natural_add n b)
end.

Compute natural_add (Successor Zero) (Successor Zero).

(* This isn't geneic over `T` like it is in the standard
library to simplify the example. *)
Inductive Vector (T :Set) : Natural -> Set :=
| Nil : Vector T Zero
| Cons (head : T) 
       (tail_length : Natural) 
       (tail : Vector T tail_length) 
       : Vector T (Successor tail_length).
       
Fixpoint append (T: Set) (n m : Natural) 
                (a : Vector T n) 
                (b : Vector T m)
                : Vector T (natural_add n m) :=
match a with
| Nil _ => b
| Cons _ head tail_length tail => 
    Cons T head (natural_add tail_length m) (append T tail_length m tail b)
end.

Compute append Natural Zero Zero (Nil Natural) (Nil Natural).

Compute append Natural 
               (Successor Zero) (Successor Zero) 
               (Cons Natural Zero Zero (Nil Natural)) 
               (Cons Natural Zero Zero (Nil Natural)).
               
End Test.


