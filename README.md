

# Universal non-indexed QITs

The following universal QITs are designed to be used in OTT with cast-on-refl, however we can also use them to encode other QITs in intensional type theory, as illustrated by the given examples. 

Apart from the universal types which are declared using postulates and rewrite rules, we only need the basic type formers Π, Σ (with η), Unit (with η), Nat, +, and equality. We also use Vec and List, but these can be defined in terms of the other types.

Differently from Fiore et al's QW type and Kovacs et al's Theory of Signatures, the data-types we can construct with these should satisfy canonicity in OTT.

- `infinitary-nonindexed-QITs/` : Universal type for infinitary non-indexed quotient inductive types. As examples, we construct MSet, SK and CTree (unordered countably-branching trees).


  DISCLAIMER: In order for the encodings to satisfy canonicity, we need η for the Unit type --- alternatively, we could consider a more complicated type for which η for Unit is not needed.

- `finitary-nonindexed-QITs/` : Universal type for finitary non-indexed quotient inductive types. As an example we construct MSet and SK.

