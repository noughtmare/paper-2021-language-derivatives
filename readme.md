*Warning:* I will probably submit this paper to ICFP 2021 and maybe TyDe 2021, so if you are on the program committee of either, please don't read below.

Paper draft: *Symbolic and Automatic Differentiation of Languages*.

**Abstract:**

Formal languages are usually defined in terms of set theory. Choosing type theory instead gives us languages as type-level predicates over strings. Applying a language to a string yields a type whose elements are language membership proofs describing *how* a string parses in the language. The usual building blocks of languages (including union, concatenation, and Kleene closure) have precise and compelling specifications uncomplicated by operational strategies and are easily generalized to a few general domain-transforming and codomain-transforming operations on predicates.

A simple characterization of languages (and indeed functions from lists to any type) captures the essential idea behind language "differentiation" and "integration" as used for recognizing languages and leads to a collection of lemmas about type-level languages. These lemmas form the backbone of two dual implementations of language recognition---(inductive) regular expressions and (coinductive) tries---each containing the same code but in dual arrangements. The language lemmas form most of the implementation in both cases, while the representation and primitive operations trade places. The regular expression version corresponds to symbolic differentiation, while the trie version corresponds to automatic differentiation.

The relatively easy-to-prove properties of type-level languages transfer almost effortlessly to the decidable implementations. In particular, despite the inductive and coinductive nature of regular expressions and tries respectively, we need neither inductive nor coinductive/bisumulation arguments to prove algebraic properties.
