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
open import Data.Nat hiding (compare)
open IsStrictTotalOrder isStrictTotalOrder

infix 10 ¬_
¬_ : Set → Set
¬ A = A → ⊥

data Key⁺ : Set where
  ⊥⁺ ⊤⁺ : Key⁺
  [_] : Key → Key⁺

infix 4 _<⁺_

data _<⁺_ : Key⁺ → Key⁺ → Set where
  b<t : ⊥⁺ <⁺ ⊤⁺
  b<x : ∀ {x} → ⊥⁺ <⁺ [ x ]
  x<t : ∀ {x} → [ x ] <⁺ ⊤⁺
  x<y : ∀ {x y} → x < y → [ x ] <⁺ [ y ]

data _≤⁺_ : Key⁺ → Key⁺ → Set where
  refl : ∀ {x} → x ≤⁺ x
  sub : ∀ {x y} → x <⁺ y → x ≤⁺ y

⊥⁺-min : ∀ {x} → ⊥⁺ ≤⁺ x
⊥⁺-min {⊥⁺} = refl
⊥⁺-min {⊤⁺} = sub b<t
⊥⁺-min {[ y ]} = sub b<x

⊤⁺-max : ∀ {x} → x ≤⁺ ⊤⁺
⊤⁺-max {⊤⁺} = refl
⊤⁺-max {⊥⁺} = sub b<t
⊤⁺-max {[ y ]} = sub x<t

trans-<⁺ : ∀ {a b c} → a <⁺ b → b <⁺ c → a <⁺ c
trans-<⁺ {[ a ]} {[ b ]} {[ c ]} (x<y a<b) (x<y b<c) = x<y (trans a<b b<c)
trans-<⁺ {⊥⁺} {_} {[ _ ]} _ _ = b<x
trans-<⁺ {⊥⁺} {_} {⊤⁺} _ _ = b<t
trans-<⁺ {[ _ ]} {_} {⊤⁺} _ _ = x<t
trans-<⁺ {a} {b = ⊥⁺} () _
trans-<⁺ {b = ⊤⁺} {c} _ ()
trans-<⁺ {a = ⊤⁺} {b} () _
trans-<⁺ {b = b} {c = ⊥⁺} _ ()

trans₁-≤⁺ : ∀ {a b c} → a <⁺ b → b ≤⁺ c → a <⁺ c
trans₁-≤⁺ prf₁ refl = prf₁
trans₁-≤⁺ prf₁ (sub prf₂) = trans-<⁺ prf₁ prf₂

trans₂-≤⁺ : ∀ {a b c} → a ≤⁺ b → b <⁺ c → a <⁺ c
trans₂-≤⁺ refl prf₁ = prf₁
trans₂-≤⁺ (sub prf₁) prf₂ = trans-<⁺ prf₁ prf₂

trans-≤⁺ : ∀ {a b c} → a ≤⁺ b → b ≤⁺ c → a ≤⁺ c
trans-≤⁺ refl refl = refl
trans-≤⁺ refl prf₁ = prf₁
trans-≤⁺ (sub prf₁) prf₂ = sub (trans₁-≤⁺ prf₁ prf₂)

_<_<_ : Key⁺ → Key → Key⁺ → Set
a < b < c = a <⁺ [ b ] × [ b ] <⁺ c

data Tree : Set where
  □ : Tree
  _«_»_ : Tree → Key → Tree → Tree

data SortedRange : Tree → Key⁺ → Key⁺ → Set where
  leaf : ∀ {min max} → min <⁺ max → SortedRange □ min max
  node : ∀ {min max l r x} →
    min < x < max →
    SortedRange l min [ x ] →
    SortedRange r [ x ] max →
    SortedRange (l « x » r) min max

Sorted : Tree → Set
Sorted t = SortedRange t ⊥⁺ ⊤⁺

lemma-extend-range : ∀ {t min₁ min₂ max₁ max₂} → min₂ ≤⁺ min₁ → max₁ ≤⁺ max₂ → SortedRange t min₁ max₁ → SortedRange t min₂ max₂
lemma-extend-range {□} prfMin prfMax (leaf prf₂) = leaf (trans₁-≤⁺ (trans₂-≤⁺ prfMin prf₂) prfMax)
lemma-extend-range {l « x » r} prfMin prfMax (node (m<x , x<m) sl sr) =
  node (trans₂-≤⁺ prfMin m<x , trans₁-≤⁺ x<m prfMax) (lemma-extend-range prfMin refl sl) (lemma-extend-range refl prfMax sr)

lemma-sorted : ∀ {t min max} → SortedRange t min max → Sorted t
lemma-sorted = lemma-extend-range ⊥⁺-min ⊤⁺-max

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

data _<[_]<_ : Key⁺ → List Key → Key⁺ → Set where
  leaf : ∀ {min max} → min <⁺ max → min <[ [] ]< max
  node : ∀ {x xs min max} → min < x < max → min <[ xs ]< max → min <[ (x ∷ xs) ]< max

lemma-concat : ∀ {xs y zs} →
  SortedList xs → ⊥⁺ <[ xs ]< [ y ] →
  SortedList zs → [ y ] <[ zs ]< ⊤⁺ →
  SortedList (xs ++ y ∷ zs)
lemma-concat {[]} {x} {[]} _ _ _ _ = tt
lemma-concat {[]} {x} {y ∷ ys} _ _ s₁ (node (x<y l₁ , _) _) = l₁ , s₁
lemma-concat {x ∷ []} {y} {zs} _ (node (_ , (x<y l₁)) _) s₂ r₂ = l₁ , lemma-concat tt (leaf b<x) s₂ r₂
lemma-concat {x ∷ x₁ ∷ xs} {y} {zs} s₁ (node _ l₁) s₂ r₂ = proj₁ s₁ , lemma-concat (proj₂ s₁) l₁ s₂ r₂

lemma-concat-range : ∀ {min max xs ys} → min <[ xs ]< max → min <[ ys ]< max → min <[ xs ++ ys ]< max
lemma-concat-range (leaf _) prf = prf
lemma-concat-range (node prfx prfxs) prfys = node prfx (lemma-concat-range prfxs prfys)

lemma-toList-range : ∀ {t min max} → SortedRange t min max → min <[ toList t ]< max
lemma-toList-range {□} (leaf prf) = leaf prf
lemma-toList-range {l « x » r} (node prfx prfl prfr) =
  lemma-concat-range
    (lemma-toList-range (lemma-extend-range refl (sub (proj₂ prfx)) prfl))
    (node prfx
    (lemma-toList-range (lemma-extend-range (sub (proj₁ prfx)) refl prfr)))

toList-sorted : ∀ {t} → Sorted t → SortedList (toList t)
toList-sorted {□} _ = tt
toList-sorted {l « x » r} (node ttt prf₁ prf₂) = 
  lemma-concat
    (toList-sorted (lemma-sorted prf₁)) (lemma-toList-range prf₁)
    (toList-sorted (lemma-sorted prf₂)) (lemma-toList-range prf₂)

splay : Tree → Key → Tree
splay □ _ = □
splay (a « x » b) k with compare k x
... | (tri≈ _ _ _) = a « x » b
splay (□ « x » a) k | (tri< _ _ _) = □ « x » a
splay ((a « y » b) « x » c) k | (tri< _ _ _) with compare k y 
... | (tri≈ _ _ _) = a « y » (b « x » c)
... | (tri> _ _ _) = {!!}
splay (((a « z » b) « y » c) « x » d) | (tri< _ _ _) | (tri< _ _ _) = {!!}
splay ((□ « y » c) « x » d) | (tri< _ _ _) | (tri< _ _ _) = {!!}
splay (a « x » □) k | (tri> _ _ _) = a « x » □
splay (a « x » (b « y » c)) k | (tri> _ _ _) with compare k y 
... | (tri≈ _ _ _) = (a « x » b) « y » c
... | (tri< _ _ _) = {!!}
... | (tri> _ _ _) = {!!}