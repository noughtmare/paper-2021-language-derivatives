\begin{code}[hide]

open import Relation.Binary.PropositionalEquality using (_≡_) ; open _≡_
open import Decidability hiding (_◂_)

module Symbolic {ℓ} {A : Set ℓ} (_≟_ : Decidable₂ {A = A} _≡_) where

open import Level
open import Data.List using ([]; _∷_)

open import Misc {ℓ}
open import Inverses {ℓ}

module ◇ where
  open import Language A public
  -- open import Predicate public ; open ListOps A public
  open import Calculus A public

open ◇ using (ν⋆; δ⋆; ν☆; δ☆; ν𝟏; δ𝟏; ν`; δ`)

private
  variable
    P Q : ◇.Lang
    s : Set ℓ
\end{code}

%<*api>
{\mathindent0ex
\begin{center}
\begin{code}[hide]
infixr  6 _∪_
infixr  7 _∩_
infixl  7 _⋆_
infixr  7 _·_
infix   9 _◂_
infixl 10 _☆
\end{code}
\begin{code}
data Lang {- (X : Set) -} : {- (X → -} ◇.Lang {- ) -} → Set (suc ℓ) where
  ∅    : Lang  ◇.∅
  𝒰    : Lang  ◇.𝒰
  _∪_  : Lang  P  → Lang Q  → Lang (P  ◇.∪  Q)
  _∩_  : Lang  P  → Lang Q  → Lang (P  ◇.∩  Q)
  _·_  : Dec   s  → Lang P  → Lang (s  ◇.·  P)
  𝟏    : Lang ◇.𝟏
  _⋆_  : Lang  P  → Lang Q  → Lang (P  ◇.⋆  Q)
  _☆   : Lang  P  → Lang (P ◇.☆)
  `    : (a : A) → Lang (◇.` a)
  _◂_  : (Q ⟷ P) → Lang P → Lang Q

open import Data.Maybe
open import Data.List using (List ; _∷_ ; [])
open import Data.Nat using (ℕ) renaming (zero to ℕzero ; suc to ℕsuc)
open import Data.Vec using (Vec ; lookup ; _∷_)
open import Data.Fin using (Fin)
open import Function using (const)

data Lang′ (n : ℕ) : (Vec ◇.Lang n → ◇.Lang) → Set (suc ℓ) where
  ∅    : Lang′ n (const ◇.∅)
  𝒰   : Lang′ n (const ◇.𝒰)
  _∪_  : ∀{P Q} → Lang′ n P  → Lang′ n Q  → Lang′ n (λ v → P v  ◇.∪  Q v)
  _∩_  : ∀{P Q} → Lang′ n P  → Lang′ n Q  → Lang′ n (λ v → P v  ◇.∩  Q v)
  _·_  : ∀{P} → Dec   s  → Lang′ n P  → Lang′ n (λ v → s ◇.·  P v)
  𝟏   : Lang′ n (const ◇.𝟏)
  _⋆_  : ∀{P Q} → Lang′ n P  → Lang′ n Q  → Lang′ n (λ v → P v  ◇.⋆  Q v)
  -- _☆   : ∀{Xs} → Lang  P  → Lang (P ◇.☆)
  `    : (a : A) → Lang′ n (const (◇.` a))
  _◂_  : ∀{P Q} → (∀{v} → Q v ⟷ P v) → Lang′ n P → Lang′ n Q
  var : (m : Fin n) → Lang′ n (λ xs → lookup xs m)
  fix : ∀{f} → Lang′ (ℕsuc n) f → Lang′ n (λ xs → ◇.fix (λ x → f (x ∷ xs)))

\end{code}
\end{center}
\iftalk
\vspace{-3.5ex}
\fi
\hfill
\begin{minipage}[c]{33ex}
\begin{code}
ν  : Lang P → Dec (◇.ν P)
δ  : Lang P → (a : A) → Lang (◇.δ P a)

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Vec.Properties

-- postulate lookup-map : ∀{ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} {f : (x : A) → B x} {n : ℕ} {v : Vec A n} {i : Fin n} → f (lookup v i) ≡ lookup (Data.Vec.map (λ r → f r) v) i

ν′ : ∀{n f} → Lang′ n f → (v : Vec (Σ[ x ∈ ◇.Lang ] Dec (◇.ν x)) n) → Dec (◇.ν (f (Data.Vec.map proj₁ v)))
ν′ ∅ _ = no (λ ())
ν′ 𝒰 _ = yes tt
ν′ (x ∪ y) v = ν′ x v ⊎‽ ν′ y v
ν′ (x ∩ y) v = ν′ x v ×‽ ν′ y v
ν′ (s · x) v = s ×‽ ν′ x v
ν′ 𝟏 _ = yes refl
ν′ (x ⋆ y) v = ν⋆ ◃ (ν′ x v ×‽ ν′ y v)
ν′ (` a) v = no (λ ())
ν′ (f ◂ x) v = f ◃ ν′ x v
ν′ (var i) v rewrite lookup-map i proj₁ v = proj₂ (lookup v i)
ν′ {f = f} (fix x) v = {!!} ◃ ν′ x ({!!} ∷ v)
-- ν′ {f = f} (fix x) v = {!!} ◃ ν′ x ((f (Data.Vec.map proj₁ v) , ν′ (fix x) v) ∷ v)
-- ν′ {f = f} (fix x) v = {!!} ◃ ν′ x ((◇.∅ , no λ ()) ∷ v)
\end{code}
\end{minipage}
\hfill
\begin{minipage}[c]{25ex}
\begin{code}
⟦_⟧‽ : Lang P → Decidable P
⟦ p ⟧‽     []    = ν p
⟦ p ⟧‽ (a  ∷ w)  = ⟦ δ p a ⟧‽ w
\end{code}
\end{minipage}
\hfill\;
}
%</api>

%<*semantics>
\begin{code}
⟦_⟧ : Lang P → ◇.Lang
⟦_⟧ {P} r = P
\end{code}
%</semantics>

%<*defs>
{\mathindent0ex
\begin{code}[hide]
private
  variable
    p : Lang P
    q : Lang Q

\end{code}
\setstretch{1.6}
\hfill
%\hspace{-1.2ex}%% To align with Automatic. Why different?
\begin{minipage}{30ex}
\begin{code}
ν ∅ = ⊥‽
ν 𝒰 = ⊤‽
ν (p ∪ q) = ν p ⊎‽ ν q
ν (p ∩ q) = ν p ×‽ ν q
ν (s · p) = s ×‽ ν p
ν 𝟏 = ν𝟏 ◃ ⊤‽
ν (p ⋆ q) = ν⋆ ◃ (ν p ×‽ ν q)
ν (p ☆) = ν☆ ◃ (ν p ✶‽)
ν (` a) = ν` ◃ ⊥‽
ν (f ◂ p) = f ◃ ν p
\end{code}
\end{minipage}
\hfill
\begin{minipage}{38ex}
\begin{code}
δ ∅ a = ∅
δ 𝒰 a = 𝒰
δ (p ∪ q) a = δ p a ∪ δ q a
δ (p ∩ q) a = δ p a ∩ δ q a
δ (s · p) a = s · δ p a
δ 𝟏 a = δ𝟏 ◂ ∅
δ (p ⋆ q) a = δ⋆ ◂ (ν p · δ q a ∪ δ p a ⋆ q)
δ (p ☆) a = δ☆ ◂ (ν p ✶‽ · (δ p a ⋆ p ☆))
δ (` c) a = δ` ◂ ((a ≟ c) · 𝟏)
δ (f ◂ p) a = f ◂ δ p a
\end{code}
\end{minipage}
\hfill\;
}
%</defs>
