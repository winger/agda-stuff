open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Level

module Splay
  {Key : Set}
  {_<_ : Rel Key Level.zero} 
  {isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_}
  where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.Nat
open IsStrictTotalOrder isStrictTotalOrder

infix 10 ¬_
¬_ : Set → Set
¬ A = A → ⊥

data Key⁺ : Set where
  ⊥⁺ ⊤⁺ : Key⁺
  [_] : Key → Key⁺

infix 4 _<⁺_

_<⁺_ : Key⁺ → Key⁺ → Set
⊥⁺ <⁺ ⊤⁺ = ⊤
⊥⁺ <⁺ [ _ ] = ⊤
[ _ ] <⁺ ⊤⁺ = ⊤
[ x ] <⁺ [ y ] = x < y
_ <⁺ _ = ⊥

⊥⁺-min : ∀ {a} → a <⁺ ⊥⁺ → ⊥
⊥⁺-min {⊥⁺} ()
⊥⁺-min {⊤⁺} ()
⊥⁺-min {[ a ]} ()

trans-<⁺ : ∀ {a b c} → a <⁺ b → b <⁺ c → a <⁺ c
trans-<⁺ {[ a ]} {[ b ]} {[ c ]} a<b b<c = trans a<b b<c
trans-<⁺ {⊥⁺} {_} {[ _ ]} _ _ = _
trans-<⁺ {⊥⁺} {_} {⊤⁺} _ _ = _
trans-<⁺ {[ _ ]} {_} {⊤⁺} _ _ = _
trans-<⁺ {a} {b = ⊥⁺} a<b _ = ⊥-elim (⊥⁺-min {a} a<b)
trans-<⁺ {b = ⊤⁺} {c} _ ()
trans-<⁺ {a = ⊤⁺} {b} () _
trans-<⁺ {b = b} {c = ⊥⁺} _ b<c = ⊥-elim (⊥⁺-min {b} b<c)

_<_<_ : Key⁺ → Key → Key⁺ → Set
a < b < c = a <⁺ [ b ] × [ b ] <⁺ c

data Tree : Set where
  □ : Tree
  _«_»_ : Tree → Key → Tree → Tree

SortedRange : Tree → Key⁺ → Key⁺ → Set
SortedRange □ min max = min <⁺ max
SortedRange (l « x » r) min max =
  min < x < max × SortedRange l min [ x ] × SortedRange r [ x ] max

Sorted : Tree → Set
Sorted t = SortedRange t ⊥⁺ ⊤⁺

size : Tree → ℕ
size □ = zero
size (l « _ » r) = suc (size l + size r)

toList : Tree → List Key
toList □ = []
toList (l « x » r) = (toList l) ++ (x ∷ toList r)

SortedList : List Key → Set
SortedList [] = ⊤
SortedList (_ ∷ []) = ⊤
SortedList (x ∷ y ∷ xs) = x < y × SortedList (y ∷ xs)

_<[_]<_ : Key⁺ → List Key → Key⁺ → Set
min <[ [] ]< max = min <⁺ max
min <[ (x ∷ xs) ]< max = min < x < max × min <[ xs ]< max

lemma-concat : ∀ {xs y zs} →
  SortedList xs → ⊥⁺ <[ xs ]< [ y ] →
  SortedList zs → [ y ] <[ zs ]< ⊤⁺ →
  SortedList (xs ++ y ∷ zs)
lemma-concat {[]} {x} {[]} _ _ _ _ = tt
lemma-concat {[]} {x} {y ∷ ys} _ _ s₁ (l₁ , _) = proj₁ l₁ , s₁
lemma-concat {x ∷ []} {y} {zs} _ ((_ , l₁) , _) s₂ r₂ =
  l₁ , lemma-concat {[]} {y} {zs} tt tt s₂ r₂
lemma-concat {x ∷ x₁ ∷ xs} {y} {zs} s₁ (_ , l₁) s₂ r₂ = 
  proj₁ s₁ , lemma-concat {x₁ ∷ xs} {y} {zs} (proj₂ s₁) l₁ s₂ r₂

--toList-sorted : (t : Tree) → Sorted t → SortedList (toList t)
--toList-sorted □ _ = tt
--toList-sorted (l « x » r) prf = {!!}

