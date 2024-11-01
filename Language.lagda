\begin{code}
{-# OPTIONS --safe --without-K #-}

module Language {ℓ} (A : Set ℓ) where

open import Level

open import Algebra.Core
-- open import Data.Empty
-- open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List using (List ; _∷_ ; [] ; _++_ ; concat ; foldr)
open import Data.Nat using (ℕ) renaming (zero to ℕzero ; suc to ℕsuc)
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Misc {ℓ}

module _ where
  open import Data.Fin using (Fin)
  open import Data.Vec using (Vec ; _∷_ ; [])
  private

    Lang : Set (suc (suc ℓ))
    Lang = List A → Set (suc ℓ)

    -- universe of language descriptions
    data Desc (n : ℕ) : Set (suc ℓ) where
      ∅ : Desc n
      𝒰 : Desc n
      _∪_ : Desc n → Desc n → Desc n
      _∩_ : Desc n → Desc n → Desc n
      _·_ : Set ℓ → Desc n → Desc n
      𝟏 : Desc n
      _⋆_ : Desc n → Desc n → Desc n
      ‵_ : A → Desc n
      var : Fin n → Desc n
      fix : Desc (ℕsuc n) → Desc n

    variable
      n : ℕ
      σ σ₁ σ₂ : Desc n
      w : List A

    -- TODO: It is annoying that we need to store the descriptions
    -- inside these environments instead of the actual semantic
    -- language itself.  Unfortunately, I couldn't figure out any
    -- other way to please the positivity checker.

    data Env : ℕ → Set (suc ℓ) where
      [] : Env 0
      _∷_ : Desc n → Env n → Env (ℕsuc n)

    lookupEnv : Env n → Fin n → ∃[ m ] Env m × Desc m
    lookupEnv (x ∷ v) Fin.zero = _ , v , x
    lookupEnv (_ ∷ v) (Fin.suc i) = lookupEnv v i

    -- semantics of language descriptions
    data Sem (v : Env n) : Desc n → Lang where
      any : Sem v 𝒰 w
      left : Sem v σ₁ w → Sem v (σ₁ ∪ σ₂) w
      right : Sem v σ₂ w → Sem v (σ₁ ∪ σ₂) w
      both : Sem v σ₁ w → Sem v σ₂ w → Sem v (σ₁ ∩ σ₂) w
      con : A → Sem v σ w → Sem v (A · σ) w
      empty : Sem v 𝟏 []
      seq : ∀{w₁ w₂} → Sem v σ₁ w₁ → Sem v σ₂ w₂ → Sem v (σ₁ ⋆ σ₂) (w₁ ++ w₂)
      symb : ∀{s} → Sem v (‵ s) (s ∷ [])
      var : (i : Fin n) → (λ (_ , v′ , σ) → Sem v′ σ w) (lookupEnv v i) → Sem v (var i) w
      step : Sem (fix σ ∷ v) σ w → Sem v (fix σ) w

    open import Data.Char

    exprDesc : (Char → A) → Desc 0
    exprDesc c = fix ((var Fin.zero ⋆ ((‵ c '+') ⋆ var Fin.zero)) ∪ (‵ c 'x'))

    exprSem : (c : Char → A) → Sem [] (exprDesc c) (c 'x' ∷ c '+' ∷ c 'x' ∷ c '+' ∷ c 'x' ∷ [])
    exprSem c = step (left (seq (var Fin.zero (step (right symb))) (seq symb (var Fin.zero (step (left (seq (var Fin.zero (step (right symb))) (seq symb (var Fin.zero (step (right symb)))))))))))

    -- It is way easier for a single variable:

    -- data Desc : Set (suc ℓ) where
    --   ∅ : Desc
    --   𝒰 : Desc
    --   _∪_ : Desc → Desc → Desc
    --   _∩_ : Desc → Desc → Desc
    --   _·_ : Set ℓ → Desc → Desc
    --   𝟏 : Desc
    --   _⋆_ : Desc → Desc → Desc
    --   ‵_ : A → Desc
    --   var : Desc -- always refers to the closest fix
    --   fix : Desc → Desc

    -- data Sem (v : Lang) : Desc → Lang where
    --   McU : Sem v 𝒰 w
    --   cup₁ : Sem v σ₁ w → Sem v (σ₁ ∪ σ₂) w
    --   cup₂ : Sem v σ₂ w → Sem v (σ₁ ∪ σ₂) w
    --   cap : Sem v σ₁ w → Sem v σ₂ w → Sem v (σ₁ ∩ σ₂) w
    --   cdot : A → Sem v σ w → Sem v (A · σ) w
    --   B1 : Sem v 𝟏 []
    --   star : ∀{w₁ w₂} → Sem v σ₁ w₁ → Sem v σ₂ w₂ → Sem v (σ₁ ⋆ σ₂) (w₁ ++ w₂)
    --   symb : ∀{s} → Sem v (‵ s) (s ∷ [])
    --   var : v w → Sem v (var) w
    --   step : Sem (Sem v (fix σ)) σ w → Sem v (fix σ) w

Lang : Set (suc ℓ)
∅ : Lang
𝒰 : Lang
_∪_ : Op₂ Lang
_∩_ : Op₂ Lang
_·_ : Set ℓ → Op₁ Lang
𝟏 : Lang
_⋆_ : Op₂ Lang
_☆ : Op₁ Lang
` : A → Lang
fix : (Lang → Lang) → Lang

infixr 6 _∪_
infixr 6 _∩_
infixl 7 _·_
infixl 7 _⋆_
infixl 10 _☆
\end{code}

%<*Lang-ops>
{
\begin{center}
\mathindent-20ex
\begin{code}
Lang = A ✶ → Set ℓ
\end{code}
\end{center}
\ifacm\else
\vspace{-3ex}
\fi
\iftalk \pause \fi
\mathindent0ex
\hfill
\begin{minipage}[t]{20ex}
\begin{code}
∅ w = ⊥

𝒰 w = ⊤

𝟏 w = w ≡ []

` c w = w ≡ c ∷ []

(s · P) w = s × P w
\end{code}
\end{minipage}
\hfill
\begin{minipage}[t]{48ex}
\begin{code}
(P ∪ Q) w = P w ⊎ Q w

(P ∩ Q) w = P w × Q w

(P ⋆ Q) w = ∃⇃ λ (u ,  v) → (w ≡ u ⊙ v) × P u × Q v

(P ☆) w = ∃ λ ws → (w ≡ concat ws) × All P ws

fix f w = ∃ λ n → go n w where
  go : ℕ → Lang
  go ℕzero = ∅
  go (ℕsuc n) = f (go n)
\end{code}
\end{minipage}
\hfill\;
}
%</Lang-ops>

\begin{code}
module AltStar where
  infixl 10 _✪
  data _✪ (P : Lang) : Lang where
    zero✪  : (P ✪) []
    suc✪   : ∀ {w} → (P ⋆ P ✪) w → (P ✪) w
\end{code}

\begin{code}
private
  module Stuff where
    private variable B X : Set ℓ
\end{code}

%<*foldr-concat>
\begin{minipage}{18em}
\begin{code}
    concat⇂ : (A ✶) ✶ → A ✶
    concat⇂ = foldr _⊙_ []
\end{code}
\end{minipage}
%% where\hspace{3em}
\begin{minipage}{18em}
\begin{code}
    foldr⇂ : (B → X → X) → X → B ✶ → X
    foldr⇂ h x []        = x
    foldr⇂ h x (b ∷ bs)  = h b (foldr⇂ h x bs)
\end{code}
\end{minipage}
%</foldr-concat>

%<*All>
\begin{code}[hide]
    infixr 5 _∷_
\end{code}
\begin{code}
    data All⇃ (P : B → Set ℓ) : B ✶ → Set ℓ where
      []   : All⇃ P []
      _∷_  : ∀ {b bs} → P b → All P bs → All⇃ P (b ∷ bs)
\end{code}
%</All>
