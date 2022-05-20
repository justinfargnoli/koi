From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.
From MetaCoq.SafeChecker Require Import Loader.

From Coq Require Extraction.

Extraction Language Haskell.

Require Coq.Vectors.VectorDef.

Print nat.
Print VectorDef.t.
Print VectorDef.append.

Recursive Extraction VectorDef.append.

Print VectorDef.t.
MetaCoq SafeCheck VectorDef.t.

MetaCoq SafeCheck (3 + 9).

Require Import Reals.

Print Rplus.
MetaCoq SafeCheck Rplus.

Module Tester.

Inductive Bool :=
| True
| False.

End Tester.

MetaCoq SafeCheck Tester.Bool.

Definition tester (v : VectorDef.t nat O) := match v with
| nil => O
| cons a v' => O
end.

Check tester.
  