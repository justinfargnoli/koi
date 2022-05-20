namespace Hidden

universe u w

inductive True : Prop where
| True : True

inductive False : Prop 

def Not (p : Prop) : Prop := False

def modus_ponens (p q : Prop) (f : p -> q) (x : p) : q :=
  f x


inductive Nat : Type 0 where 
| zero : Nat
| succ : Nat -> Nat

def one : Nat := Nat.succ Nat.zero

def add (a b : Nat) : Nat :=
  match a with
    | Nat.zero => b
    | Nat.succ (n : Nat) => Nat.succ (add n b)

def subtract (a b : Nat) : Nat :=
  match b with  
    | Nat.zero => a
    | Nat.succ (bn : Nat) => match a with 
      | Nat.zero => a
      | Nat.succ (an : Nat) => subtract an bn  


inductive List (A : Type u) : Type u where
| nil : List A
| cons : A -> List A -> List A

def length (A: Type u) (l : List A) : Nat :=
  match l with
    | List.nil => Nat.zero
    | List.cons (x : A) (xs : List A) => Nat.succ (length A xs)

def append (A : Type u) (B : Type w) (f : A -> B) (as : List A) (bs : List B) : List B := 
  match as with
    | List.nil => bs
    | List.cons (x : A) (xs : List A) => append A B f xs (List.cons (f x) bs)
#print append
#check append

inductive Vector (A : Type u) : Nat -> Type u where
| nil : Vector A Nat.zero
| cons : A -> (tail_length : Nat) -> Vector A tail_length -> Vector A (Nat.succ tail_length)

def vector_append (A : Type u) (n m : Nat) (a : Vector A n) (b : Vector A m) : Vector A (add n m) := 
  match a with
    | Vector.nil => b
    | Vector.cons head tail_length tail => 
        Vector.cons head (add tail_length m) (vector_append A tail_length m tail b)

-- theorem length_nil : length List.nil = Nat.zero := by rfl


-- Defines a function that takes a name and produces a greeting.
def getGreeting (name : String) := s!"Hello, {name}! Isn't Lean great?"

def run : IO Unit := 
  -- Define a list of names
  let names := ["Sebastian", "Leo", "Daniel"]

  -- Map each name to a greeting
  let greetings := names.map Hidden.getGreeting

  -- Print the list of greetings
  for greeting in greetings do
    IO.println greeting

end Hidden

def main : IO Unit :=
  Hidden.run

inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true
-- #print numberOfDay
-- #print numberOfDay.match_1
-- #print Weekday.casesOn
-- #check @Weekday.rec
/-
@Weekday.rec.{u}
 : {motive : Weekday → Sort u} →
    motive Weekday.sunday →
    motive Weekday.monday →
    motive Weekday.tuesday →
    motive Weekday.wednesday →
    motive Weekday.thursday →
    motive Weekday.friday →
    motive Weekday.saturday →
    (t : Weekday) → motive t
-/

-- #check List