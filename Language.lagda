\begin{code}
module Language (A : Set) where

open import Level

open import Algebra.Core
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Misc

Lang : Set₁
∅ : Lang
𝒰 : Lang
_∪_ : Op₂ Lang
_∩_ : Op₂ Lang
_·_ : Set → Op₁ Lang
𝟏 : Lang
_⋆_ : Op₂ Lang
` : A → Lang

infixr 6 _∪_
infixr 6 _∩_
infixl 7 _·_
infixl 7 _⋆_
infixl 10 _☆
\end{code}

%<*Lang>
\begin{code}
Lang = A ✶ → Set
\end{code}
%</Lang>

%<*Lang-ops>
{\mathindent0ex
\hfill
\begin{minipage}[t]{20ex}
\begin{code}
∅ w = ⊥

𝒰 w = ⊤

𝟏 w = w ≡ []

` c w = w ≡ [ c ]

(s · P) w = s × P w
\end{code}
\end{minipage}
\hfill
\begin{minipage}[t]{48ex}
\begin{code}
(P ∪ Q) w = P w ⊎ Q w

(P ∩ Q) w = P w × Q w

(P ⋆ Q) w = ∃⇃ λ (u ,  v) → (w ≡ u ⊙ v) × P u × Q v

data _☆ (P : Lang) : Lang where
  zero☆  : (P ☆) []
  suc☆   : ∀ {w} → (P ⋆ P ☆) w → (P ☆) w
\end{code}
\end{minipage}
\hfill\;
}
%</Lang-ops>