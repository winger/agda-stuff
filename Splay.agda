open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; inspect; refl)
open import Function.Equivalence as Eq using (_⇔_; equivalence)
import Level

module Splay
  {Key : Set}
  {_<_ : Rel Key Level.zero} 
  {isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_}
  where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.Nat hiding (compare)
open IsStrictTotalOrder isStrictTotalOrder

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

lemma-¬[x]<[y] : ∀ {x y} → ¬ x < y → ¬ [ x ] <⁺ [ y ]
lemma-¬[x]<[y] prf (x<y prf₁) = prf prf₁

lemma-x≡y : {x y : Key} → (Key⁺.[_] x) ≡ [ y ] → x ≡ y
lemma-x≡y {x} {.x} refl = refl

compare⁺ : Trichotomous _≡_ _<⁺_
compare⁺ [ x ] [ y ] with compare x y 
compare⁺ [ x ] [ .x ] | (tri≈ prf₁ refl prf₃) = tri≈ (lemma-¬[x]<[y] prf₃) refl (lemma-¬[x]<[y] prf₃)
... | (tri< prf₁ prf₂ prf₃) = tri< (x<y prf₁) (λ prf → prf₂ (lemma-x≡y prf)) (lemma-¬[x]<[y] prf₃)
... | (tri> prf₁ prf₂ prf₃) = tri> (lemma-¬[x]<[y] prf₁) (λ prf → prf₂ (lemma-x≡y prf)) (x<y prf₃)
compare⁺ ⊥⁺ ⊥⁺ = tri≈ (λ ()) refl (λ ())
compare⁺ ⊤⁺ ⊤⁺ = tri≈ (λ ()) refl (λ ())
compare⁺ ⊥⁺ [ x ] = tri< b<x (λ ()) (λ ())
compare⁺ [ x ] ⊥⁺ = tri> (λ ()) (λ ()) b<x
compare⁺ ⊥⁺ ⊤⁺ = tri< b<t (λ ()) (λ ())
compare⁺ ⊤⁺ [ x ] = tri> (λ ()) (λ ()) x<t
compare⁺ [ x ] ⊤⁺ = tri< x<t (λ ()) (λ ())
compare⁺ ⊤⁺ ⊥⁺ = tri> (λ ()) (λ ()) b<t

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

lookup-zip-tr : Key⁺ → Tree → TreeZipper → Tree × TreeZipper
lookup-zip-tr _ □ zip = (□ , zip)
lookup-zip-tr y (l « x » r) zip with compare⁺ y [ x ]
... | (tri< _ _ _) = lookup-zip-tr y l (?« x » r ∷ zip)
... | (tri≈ _ _ _) = l « x » r , zip
... | (tri> _ _ _) = lookup-zip-tr y r (l « x »? ∷ zip)

lookup-zip : Key⁺ → Tree → Tree × TreeZipper
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

lemma-range : ∀ {min max t} → SortedRange t min max → min <⁺ max
lemma-range (leaf prf) = prf
lemma-range (node (prf₁ , prf₂) _ _) = trans-<⁺ prf₁ prf₂

sorted-lookup-zip-tr : ∀ {min max t y zip} → SortedRange t min max → SortedRangeZipper zip min max → min < y < max → ∃₂ λ (min₁ max₁ : Key⁺) → SortedRangeZipper (proj₂ (lookup-zip-tr [ y ] t zip)) min₁ max₁ × SortedRange (proj₁ (lookup-zip-tr [ y ] t zip)) min₁ max₁ × min₁ < y < max₁
sorted-lookup-zip-tr {min} {max} {□} prf₁ prf₂ prf₃ = min , max , prf₂ , prf₁ , prf₃
sorted-lookup-zip-tr {min} {max} {a « x » b} {y} {zip} (node prf₁ prf₂ prf₃) prfZip prfSeg with compare⁺ [ y ] [ x ]
... | (tri≈ _ _ _) = min , max , prfZip , node prf₁ prf₂ prf₃ , prfSeg
... | (tri< prf< _ _) = sorted-lookup-zip-tr prf₂ (?«» prfZip prf₃) (proj₁ prfSeg , prf<)
... | (tri> _ _ prf>) = sorted-lookup-zip-tr prf₃ («»? prfZip prf₂) (prf> , proj₂ prfSeg)

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

insert : Key → Tree → Tree
insert x a with lookup-zip [ x ] a
... | (□ , zip) = splay (□ « x » □) zip
... | (b , zip) = splay b zip

delete : Key → Tree → Tree
delete x a with lookup-zip [ x ] a
... | (□ , zip) = splay □ zip
... | (b « y » c , zip) with (lookup-zip ⊤⁺) b | inspect (λ x → proj₁ (lookup-zip ⊤⁺ x)) b
... | (□ , zip₁) | _ = splay (splay c zip₁) zip
... | (_ « _ » _ , _) | (P.[_] eq) = ⊥-elim (lemma-lookup-⊤⁺ b eq)
  where lemma-lookup-⊤⁺ : ∀ {zip b c x} (a : Tree) → proj₁ (lookup-zip-tr ⊤⁺ a zip) ≢ (b « x » c)
        lemma-lookup-⊤⁺ □ ()
        lemma-lookup-⊤⁺ (d « y » e) prf with compare⁺ ⊤⁺ [ y ]
        ... | (tri< () _ _)
        ... | (tri≈ _ () _)
        ... | (tri> _ _ _) = lemma-lookup-⊤⁺ e prf

data _∈_ : Key → Tree → Set where
  root : ∀ {x a b} → x ∈ (a « x » b)
  left : ∀ {x y a b} → x ∈ a → x ∈ (a « y » b)
  right : ∀ {x y a b} → x ∈ b → x ∈ (a « y » b)

lemma-in-range : ∀ {x a min max} → x ∈ a → SortedRange a min max → min < x < max
lemma-in-range root (node prf _ _) = prf
lemma-in-range {x} {a « y » b} (left prf₀) (node prf₁ prf₂ prf₃) = proj₁ (lemma-in-range prf₀ prf₂) , trans-<⁺ (proj₂ (lemma-in-range prf₀ prf₂)) (proj₂ prf₁)
lemma-in-range {x} {a « y » b} (right prf₀) (node prf₁ prf₂ prf₃) = trans-<⁺ (proj₁ prf₁) (proj₁ (lemma-in-range prf₀ prf₃)) , proj₂ (lemma-in-range prf₀ prf₃)

data _∈zip_ : Key → TreeZipper → Set where
  hd-?«» : ∀ {x y t zip} → x ∈ t → x ∈zip (?« y » t ∷ zip)
  hd-«»? : ∀ {x y t zip} → x ∈ t → x ∈zip (t « y »? ∷ zip)
  hd-?«»-≡ : ∀ {x t zip} → x ∈zip (?« x » t ∷ zip) 
  hd-«»?-≡ : ∀ {x t zip} → x ∈zip (t « x »? ∷ zip)
  tl : ∀ {x h zip} → x ∈zip zip → x ∈zip (h ∷ zip)

lemma-lookup-zip-tr₁ : ∀ {x y zip} → ∀ a → x ∈zip zip → x ∈zip proj₂ (lookup-zip-tr y a zip)
lemma-lookup-zip-tr₁ □ prf = prf
lemma-lookup-zip-tr₁ {y = y} (a « z » b) prf with compare⁺ y [ z ]
... | (tri≈ _ _ _) = prf
... | (tri< _ _ _) = lemma-lookup-zip-tr₁ a (tl prf)
... | (tri> _ _ _) = lemma-lookup-zip-tr₁ b (tl prf)

lemma-lookup-zip-tr₂ : ∀ {x} → ∀ y → ∀ a → ∀ zip → x ∈zip proj₂ (lookup-zip-tr y a zip) → x ∈ a
lemma-lookup-zip-tr₂ = {!!}

lemma-lookup-zip-tr : ∀ {a x} → (y : Key⁺) → (zip : TreeZipper) → x ∈ a → x ∈ proj₁ (lookup-zip-tr y a zip) ⊎ x ∈zip proj₂ (lookup-zip-tr y a zip)
lemma-lookup-zip-tr {□} _ _ ()
lemma-lookup-zip-tr {b « .x » c} {x} y zip root with compare⁺ y [ x ]
... | (tri≈ _ _ _) = inj₁ root
... | (tri< _ _ _) = inj₂ (lemma-lookup-zip-tr₁ b (hd-?«»-≡ {x} {c} {zip}))
... | (tri> _ _ _) = inj₂ (lemma-lookup-zip-tr₁ c (hd-«»?-≡ {x} {b} {zip}))
lemma-lookup-zip-tr {b « z » c} y zip (left prf) with compare⁺ y [ z ]
... | (tri≈ _ _ _) = inj₁ (left prf)
... | (tri< _ _ _) = lemma-lookup-zip-tr y (?« z » c ∷ zip) prf
... | (tri> _ _ _) = inj₂ (lemma-lookup-zip-tr₁ c (hd-«»? prf))
lemma-lookup-zip-tr {b « z » c} y zip (right prf) with compare⁺ y [ z ]
... | (tri≈ _ _ _) = inj₁ (right prf)
... | (tri< _ _ _) = inj₂ (lemma-lookup-zip-tr₁ b (hd-?«» prf))
... | (tri> _ _ _) = lemma-lookup-zip-tr y (b « z »? ∷ zip) prf

lemma-∈-splay₁ : ∀ {a x} → ∀ zip → x ∈ a → x ∈ splay a zip
lemma-∈-splay₁ {a} [] prf = prf
lemma-∈-splay₁ {□} _ ()
--zig
lemma-∈-splay₁ {a « x » b} (?« y » c ∷ []) root = root
lemma-∈-splay₁ {a « x » b} (?« y » c ∷ []) (left prf) = left prf
lemma-∈-splay₁ {a « x » b} (?« y » c ∷ []) (right prf) = right (left prf)
lemma-∈-splay₁ {a « x » b} (c « y »? ∷ []) root = root
lemma-∈-splay₁ {a « x » b} (c « y »? ∷ []) (left prf) = left (right prf)
lemma-∈-splay₁ {a « x » b} (c « y »? ∷ []) (right prf) = right prf
--zig-zig
lemma-∈-splay₁ {a « x » b} (?« y » c ∷ ?« z » d ∷ zip) root = lemma-∈-splay₁ zip root
lemma-∈-splay₁ {a « x » b} (?« y » c ∷ ?« z » d ∷ zip) (left prf) = lemma-∈-splay₁ zip (left prf)
lemma-∈-splay₁ {a « x » b} (?« y » c ∷ ?« z » d ∷ zip) (right prf) = lemma-∈-splay₁ zip (right (left prf))
lemma-∈-splay₁ {c « x » d} (b « y »? ∷ a « z »? ∷ zip) root = lemma-∈-splay₁ zip root
lemma-∈-splay₁ {c « x » d} (b « y »? ∷ a « z »? ∷ zip) (left prf) = lemma-∈-splay₁ zip (left (right prf))
lemma-∈-splay₁ {c « x » d} (b « y »? ∷ a « z »? ∷ zip) (right prf) = lemma-∈-splay₁ zip (right prf)
--zig-zag
lemma-∈-splay₁ {b « x » c} (a « y »? ∷ ?« z » d ∷ zip) root = lemma-∈-splay₁ zip root
lemma-∈-splay₁ {b « x » c} (a « y »? ∷ ?« z » d ∷ zip) (left prf) = lemma-∈-splay₁ zip (left (right prf))
lemma-∈-splay₁ {b « x » c} (a « y »? ∷ ?« z » d ∷ zip) (right prf) = lemma-∈-splay₁ zip (right (left prf))
lemma-∈-splay₁ {b « x » c} (?« y » d ∷ a « z »? ∷ zip) root = lemma-∈-splay₁ zip root
lemma-∈-splay₁ {b « x » c} (?« y » d ∷ a « z »? ∷ zip) (left prf) = lemma-∈-splay₁ zip (left (right prf))
lemma-∈-splay₁ {b « x » c} (?« y » d ∷ a « z »? ∷ zip) (right prf) = lemma-∈-splay₁ zip (right (left prf))

lemma-∈-splay₂ : ∀ {x} → ∀ a → ∀ zip → x ∈zip zip → x ∈ splay a zip
lemma-∈-splay₂ _ [] ()
lemma-∈-splay₂ □ (?« x » a ∷ zip) hd-?«»-≡ = lemma-∈-splay₁ zip root
lemma-∈-splay₂ □ (?« x » a ∷ zip) (hd-?«» prf) = lemma-∈-splay₁ zip (right prf)
lemma-∈-splay₂ □ (?« x » a ∷ zip) (tl prf) = lemma-∈-splay₂ _ zip prf
lemma-∈-splay₂ □ (a « x »? ∷ zip) hd-«»?-≡ = lemma-∈-splay₁ zip root
lemma-∈-splay₂ □ (a « x »? ∷ zip) (hd-«»? prf) = lemma-∈-splay₁ zip (left prf)
lemma-∈-splay₂ □ (a « x »? ∷ zip) (tl prf) = lemma-∈-splay₂ _ zip prf
--zig
lemma-∈-splay₂ (a « x » b) (?« y » c ∷ []) hd-?«»-≡ = right root
lemma-∈-splay₂ (a « x » b) (?« y » c ∷ []) (hd-?«» prf) = right (right prf)
lemma-∈-splay₂ (a « x » b) (?« y » c ∷ []) (tl ())
lemma-∈-splay₂ (b « x » c) (a « y »? ∷ []) hd-«»?-≡ = left root
lemma-∈-splay₂ (b « x » c) (a « y »? ∷ []) (hd-«»? prf) = left (left prf)
lemma-∈-splay₂ (b « x » c) (a « y »? ∷ []) (tl ())
--zig-zig
lemma-∈-splay₂ (a « x » b) (?« y » c ∷ ?« z » d ∷ zip) hd-?«»-≡ = lemma-∈-splay₁ zip (right root)
lemma-∈-splay₂ (a « x » b) (?« y » c ∷ ?« z » d ∷ zip) (hd-?«» prf) = lemma-∈-splay₁ zip (right (right (left prf)))
lemma-∈-splay₂ (a « x » b) (?« y » c ∷ ?« z » d ∷ zip) (tl hd-?«»-≡) = lemma-∈-splay₁ zip (right (right root))
lemma-∈-splay₂ (a « x » b) (?« y » c ∷ ?« z » d ∷ zip) (tl (hd-?«» prf)) = lemma-∈-splay₁ zip (right (right (right prf)))
lemma-∈-splay₂ (a « x » b) (?« y » c ∷ ?« z » d ∷ zip) (tl (tl prf)) = lemma-∈-splay₂ _ zip prf
lemma-∈-splay₂ (c « x » d) (b « y »? ∷ a « z »? ∷ zip) hd-«»?-≡ = lemma-∈-splay₁ zip (left root)
lemma-∈-splay₂ (c « x » d) (b « y »? ∷ a « z »? ∷ zip) (hd-«»? prf) = lemma-∈-splay₁ zip (left (left (right prf)))
lemma-∈-splay₂ (c « x » d) (b « y »? ∷ a « z »? ∷ zip) (tl hd-«»?-≡) = lemma-∈-splay₁ zip (left (left root))
lemma-∈-splay₂ (c « x » d) (b « y »? ∷ a « z »? ∷ zip) (tl (hd-«»? prf)) = lemma-∈-splay₁ zip (left (left (left prf)))
lemma-∈-splay₂ (c « x » d) (b « y »? ∷ a « z »? ∷ zip) (tl (tl prf)) = lemma-∈-splay₂ _ zip prf
--zig-zag
lemma-∈-splay₂ (b « x » c) (a « y »? ∷ ?« z » d ∷ zip) hd-«»?-≡ = lemma-∈-splay₁ zip (left root)
lemma-∈-splay₂ (b « x » c) (a « y »? ∷ ?« z » d ∷ zip) (hd-«»? prf) = lemma-∈-splay₁ zip (left (left prf))
lemma-∈-splay₂ (b « x » c) (a « y »? ∷ ?« z » d ∷ zip) (tl hd-?«»-≡) = lemma-∈-splay₁ zip (right root)
lemma-∈-splay₂ (b « x » c) (a « y »? ∷ ?« z » d ∷ zip) (tl (hd-?«» prf)) = lemma-∈-splay₁ zip (right (right prf))
lemma-∈-splay₂ (b « x » c) (a « y »? ∷ ?« z » d ∷ zip) (tl (tl prf)) = lemma-∈-splay₂ _ zip prf
lemma-∈-splay₂ (b « x » c) (?« y » d ∷ a « z »? ∷ zip) (hd-?«»-≡) = lemma-∈-splay₁ zip (right root)
lemma-∈-splay₂ (b « x » c) (?« y » d ∷ a « z »? ∷ zip) (hd-?«» prf) = lemma-∈-splay₁ zip (right (right prf))
lemma-∈-splay₂ (b « x » c) (?« y » d ∷ a « z »? ∷ zip) (tl hd-«»?-≡) = lemma-∈-splay₁ zip (left root)
lemma-∈-splay₂ (b « x » c) (?« y » d ∷ a « z »? ∷ zip) (tl (hd-«»? prf)) = lemma-∈-splay₁ zip (left (left prf))
lemma-∈-splay₂ (b « x » c) (?« y » d ∷ a « z »? ∷ zip) (tl (tl prf)) = lemma-∈-splay₂ _ zip prf

lemma-∈-splay₃ : ∀ {x} → ∀ a → ∀ zip → x ∈ splay a zip → x ∈ a ⊎ x ∈zip zip
lemma-∈-splay₃ a zip prf = {!!}

lemma-lookup : ∀ {x y a b c zip} → proj₁ (lookup-zip-tr [ x ] a zip) ≡ (b « y » c) → x ≡ y
lemma-lookup {a = □} ()
lemma-lookup {x} {y} {d « z » e} {zip = zip} eq with compare⁺ [ x ] [ z ]
lemma-lookup {x} {y} {._ « .y » ._} refl | (tri≈ _ prf _) = lemma-x≡y prf
... | (tri< _ _ _) = lemma-lookup {a = d} eq
... | (tri> _ _ _) = lemma-lookup {a = e} eq

lemma-insert₁ : (x : Key) → (a : Tree) → x ∈ insert x a
lemma-insert₁ x a with lookup-zip [ x ] a | inspect (λ t → proj₁ (lookup-zip [ x ] t)) a
... | (□ , zip) | _ = lemma-∈-splay₁ zip root
... | (b « y » c , zip) | (P.[_] eq) with lemma-lookup {a = a} eq
... | eq₁ = lemma-∈-splay₁ zip (tmp eq₁)
  where tmp : ∀ {x y a b} → x ≡ y → x ∈ (a « y » b)
        tmp {x} {.x} refl = root

lemma-insert₂ : ∀ {x a} → (y : Key) → x ∈ a → x ∈ insert y a
lemma-insert₂ {x} {a} y prf with lookup-zip [ y ] a | lemma-lookup-zip-tr [ y ] [] prf
... | (□ , zip) | (inj₁ ())
... | (□ , zip) | (inj₂ prf₁) = lemma-∈-splay₂ _ zip prf₁
... | (b « z » c , zip) | (inj₁ prf₁) = lemma-∈-splay₁ zip prf₁
... | (b « z » c , zip) | (inj₂ prf₁) = lemma-∈-splay₂ _ zip prf₁

lemma-insert₃ : ∀ {x y a} → x ∈ insert y a → x ∈ a ⊎ x ≡ y
lemma-insert₃ {x} {y} {a} prf with lookup-zip [ y ] a | inspect (λ t → proj₂ (lookup-zip [ y ] t)) a
... | (□ , zip) | (P.[_] eq) = tmp (lemma-∈-splay₃ (□ « y » □) zip prf) eq
  where tmp : ∀ {x y zip a} → x ∈ (□ « y » □) ⊎ x ∈zip zip → proj₂ (lookup-zip-tr [ y ] a []) ≡ zip → x ∈ a ⊎ x ≡ y
        tmp {x} {.x} (inj₁ root) _ = inj₂ refl
        tmp (inj₁ (left ())) _
        tmp (inj₁ (right ())) _
        tmp {x} {y} {a = a} (inj₂ prf₁) eq = inj₁ (lemma-lookup-zip-tr₂ [ y ] a [] (P.subst (λ t → x ∈zip t) (P.sym eq) prf₁))
... | (b « z » c , zip) | (P.[_] eq) = {!!}


theorem-insert₁ : ∀ {x a} → Sorted a → Sorted (insert x a)
theorem-insert₁ {x} {a} prf with lookup-zip [ x ] a | sorted-lookup-zip-tr {⊥⁺} {⊤⁺} {a} {x} {[]} prf [] (b<x , x<t)
... | □ , zip | min , max , prf₁ , prf₂ , prf₃ = sorted-splay (node prf₃ (leaf (proj₁ prf₃)) (leaf (proj₂ prf₃))) prf₁
... | b « z » c , zip | min , max , prf₁ , prf₂ , _ = sorted-splay prf₂ prf₁

theorem-insert₂ : ∀ {x y a} → (x ∈ a ⊎ x ≡ y) ⇔ (x ∈ insert y a)
theorem-insert₂ = equivalence to lemma-insert₃
  where to : ∀ {x y a} → x ∈ a ⊎ x ≡ y → x ∈ insert y a
        to {y = y} (inj₁ prf) = lemma-insert₂ y prf
        to {x} {.x} {a} (inj₂ refl) = lemma-insert₁ x a

theorem-delete₁ : ∀ {x a} → Sorted a → Sorted (delete x a)
theorem-delete₁ = {!!}

theorem-delete₂ : ∀ {x y a} → (x ∈ a) ⇔ (x ∈ delete y a ⊎ x ≡ y)
theorem-delete₂ = equivalence {!!} {!!}