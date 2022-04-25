type nat =
| O
| S of nat

let rec add n m =
  match n with
  | O -> m
  | S x -> S (add x m)

type 'a vector =
| Nil
| Cons of 'a * nat * 'a vector

let rec append _unused_a_length b_length a b =
  match a with
  | Nil -> b
  | Cons (x, v_length, v) -> Cons (x, 
            (add v_length b_length), 
            (append v_length b_length v b))