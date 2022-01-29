namespace Hidden

universe u

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


inductive List : Type u where
| nil : List
| cons : Nat -> List -> List 

def length (l : List) : Nat :=
  match l with
    | List.nil => Nat.zero
    | List.cons (x : Nat) (xs : List) => Nat.succ (length xs)

def append (as : List) (bs : List) : List := 
  match as with
    | List.nil => bs
    | List.cons (x : Nat) (xs : List) => append xs (List.cons x bs)

theorem length_nil : length List.nil = Nat.zero := by rfl


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
#print numberOfDay
-- ... numberOfDay.match_1
#print numberOfDay.match_1
-- ... Weekday.casesOn ...
#print Weekday.casesOn
-- ... Weekday.rec ...
#check @Weekday.rec
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

#check List