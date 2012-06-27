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

data Tree' : Set where
  ?«_»_ : Key → Tree → Tree'
  _«_»? : Tree → Key → Tree'

TreeZipper : Set
TreeZipper = List Tree'

lookup-zip-tr : Key → Tree → TreeZipper → Tree × TreeZipper
lookup-zip-tr _ □ zip = (□ , zip)
lookup-zip-tr y (l « x » r) zip with compare y x
... | (tri< _ _ _) = lookup-zip-tr y l (?« x » r ∷ zip)
... | (tri≈ _ _ _) = l « x » r , zip
... | (tri> _ _ _) = lookup-zip-tr y r (l « x »? ∷ zip)

lookup-zip : Key → Tree → Tree × TreeZipper
lookup-zip x t = lookup-zip-tr x t []

data SortedRangeZipper : TreeZipper → Key⁺ → Key⁺ → Set where
  [] : SortedRangeZipper [] ⊥⁺ ⊤⁺
  ?«» : ∀ {min max zip x a} →
    SortedRangeZipper zip min max →
    SortedRange a [ x ] max →
    SortedRangeZipper (?« x » a ∷ zip) min [ x ]
  «»? : ∀ {min max zip x a} →
    SortedRangeZipper zip min max →
    SortedRange a min [ x ] →
    SortedRangeZipper (a « x »? ∷ zip) [ x ] max

sorted-lookup-zip-tr : ∀ {min max t y zip} → SortedRange t min max → SortedRangeZipper zip min max → ∃₂ λ (min₁ max₁ : Key⁺) → SortedRangeZipper (proj₂ (lookup-zip-tr y t zip)) min₁ max₁ × SortedRange (proj₁ (lookup-zip-tr y t zip)) min₁ max₁
sorted-lookup-zip-tr {min} {max} {□} prf₁ prf₂ = min , max , prf₂ , prf₁
sorted-lookup-zip-tr {min} {max} {a « x » b} {y} {zip} (node prf₁ prf₂ prf₃) prfZip with compare y x
... | (tri≈ _ _ _) = min , max , prfZip , node prf₁ prf₂ prf₃
... | (tri< _ _ _) = sorted-lookup-zip-tr prf₂ (?«» prfZip prf₃)
... | (tri> _ _ _) = sorted-lookup-zip-tr prf₃ («»? prfZip prf₂)

splay : Tree → TreeZipper → Tree
splay a [] = a
splay □ (?« x » a ∷ zip) = splay (□ « x » a) zip
splay □ (a « x »? ∷ zip) = splay (a « x » □) zip
--zig
splay (a « x » b) (?« y » c ∷ []) = a « x » (b « y » c)
splay (b « x » c) (a « y »? ∷ []) = (a « y » b) « x » c
--zig-zig
splay (a « x » b) (?« y » c ∷ ?« z » d ∷ zip) = splay (a « x » (b « y » (c « z » d))) zip
splay (c « x » d) (b « y »? ∷ a « z »? ∷ zip) = splay (((a « z » b) « y » c) « x » d) zip
--zig-zag
splay (b « x » c) (a « y »? ∷ ?« z » d ∷ zip) = splay ((a « y » b) « x » (c « z » d)) zip
splay (b « x » c) (?« y » d ∷ a « z »? ∷ zip) = splay ((a « z » b) « x » (c « y » d)) zip

lemma-range : ∀ {min max t} → SortedRange t min max → min <⁺ max
lemma-range (leaf prf) = prf
lemma-range (node (prf₁ , prf₂) _ _) = trans-<⁺ prf₁ prf₂

sorted-splay : ∀ {min max t zip} → SortedRange t min max → SortedRangeZipper zip min max → Sorted (splay t zip)
sorted-splay {zip = []} prf₁ _ = lemma-extend-range ⊥⁺-min ⊤⁺-max prf₁
sorted-splay {t = □} {zip = ?« x » a ∷ zip} prf₁ (?«» prf₂ prf₃) = sorted-splay (node (lemma-range prf₁ , lemma-range prf₃) prf₁ prf₃) prf₂
sorted-splay {t = □} {zip = a « x »? ∷ zip} prf₁ («»? prf₂ prf₃) = sorted-splay (node (lemma-range prf₃ , lemma-range prf₁) prf₃ prf₁) prf₂
--zig
sorted-splay {t = a « x » b} {zip = ?« y » c ∷ []} (node p₀ p₁ p₂) (?«» prf₂ prf₃) = sorted-splay (node (proj₁ p₀ , trans-<⁺ (proj₂ p₀) (lemma-range prf₃)) p₁ (node (proj₂ p₀ , lemma-range prf₃) p₂ prf₃)) prf₂
sorted-splay {t = b « x » c} {zip = a « y »? ∷ []} (node p₀ p₁ p₂) («»? prf₂ prf₃) = sorted-splay (node (trans-<⁺ (lemma-range prf₃) (proj₁ p₀) , proj₂ p₀) (node (lemma-range prf₃ , proj₁ p₀) prf₃ p₁) p₂) prf₂
--zig-zig
sorted-splay {t = a « x » b} {zip = ?« y » c ∷ ?« z » d ∷ zip} (node p₀ p₁ p₂) (?«» (?«» prf₂ prf₃) prf₄) = sorted-splay (node (proj₁ p₀ , trans-<⁺ (proj₂ p₀) (trans-<⁺ (lemma-range prf₄) (lemma-range prf₃))) p₁ (node ((proj₂ p₀) , (trans-<⁺ (lemma-range prf₄) (lemma-range prf₃))) p₂ (node (lemma-range prf₄ , lemma-range prf₃) prf₄ prf₃))) prf₂
sorted-splay {t = c « x » d} {zip = b « y »? ∷ a « z »? ∷ zip} (node p₀ p₁ p₂) («»? («»? prf₂ prf₃) prf₄) = sorted-splay (node ((trans-<⁺ (lemma-range prf₃) (trans-<⁺ (lemma-range prf₄) (proj₁ p₀))) , (proj₂ p₀)) (node ((trans-<⁺ (lemma-range prf₃) (lemma-range prf₄)) , (proj₁ p₀)) (node ((lemma-range prf₃) , (lemma-range prf₄)) prf₃ prf₄) p₁) p₂) prf₂
--zig-zag
sorted-splay {t = b « x » c} {zip = a « y »? ∷ ?« z » d ∷ zip} (node p₀ p₁ p₂) («»? (?«» prf₂ prf₃) prf₄) = sorted-splay (node ((trans-<⁺ (lemma-range prf₄) (proj₁ p₀)) , (trans-<⁺ (proj₂ p₀) (lemma-range prf₃))) (node ((lemma-range prf₄) , (proj₁ p₀)) prf₄ p₁) (node (lemma-range p₂ , lemma-range prf₃) p₂ prf₃)) prf₂
sorted-splay {t = b « x » c} {zip = ?« y » d ∷ a « z »? ∷ zip} (node p₀ p₁ p₂) (?«» («»? prf₂ prf₃) prf₄) = sorted-splay (node ((trans-<⁺ (lemma-range prf₃) (proj₁ p₀)) , (trans-<⁺ (proj₂ p₀) (lemma-range prf₄))) (node (lemma-range prf₃ , proj₁ p₀) prf₃ p₁) (node (lemma-range p₂ , lemma-range prf₄) p₂ prf₄)) prf₂

