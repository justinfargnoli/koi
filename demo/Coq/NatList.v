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