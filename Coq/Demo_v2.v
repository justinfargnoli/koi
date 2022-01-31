From Coq Require Extraction.

Extraction Language Haskell.

Require Coq.Vectors.VectorDef.

Print nat.
Print VectorDef.t.
Print VectorDef.append.

Recursive Extraction VectorDef.append.
  