module Test where

data Nat = O | S Nat 

add :: Nat -> Nat -> Nat 
add n m = case n of { 
  O -> m; 
  S p -> S (add p m)
} 

data Vector a = Nil | Cons a Nat (Vector a) 

append :: Nat -> Nat -> (Vector a1) -> (Vector a1) -> Vector a1 
append _ p v w = case v of { 
  Nil -> w; 
  Cons a n0 v' -> Cons a (add n0 p) (append n0 p v' w)
}

