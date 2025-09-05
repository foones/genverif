open import Data.Nat using (ℕ; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)

Id : Set
Id = ℕ

data Preterm : Set where
  var : Id → Preterm
  lam : Id → Preterm → Preterm
  app : Preterm → Preterm → Preterm

data isFV : Id → Preterm → Set where
  isFV-var : ∀ {x} → isFV x (var x)
  isFV-lam : ∀ {x y t} → x ≢ y → isFV x t → isFV x (lam y t)
  isFV-app₁ : ∀ {x t s} → isFV x t → isFV x (app t s)
  isFV-app₂ : ∀ {x t s} → isFV x s → isFV x (app t s)

data _[_:=_]=_ : Preterm → Id → Preterm → Preterm → Set where
  sub-var₁ : ∀ {x t} → (var x) [ x := t ]= t
  sub-var₂ : ∀ {x y t} → x ≢ y → var y [ x := t ]= var y
  sub-app : ∀ {t₁ t₂ x s t₁' t₂'}
            → t₁ [ x := s ]= t₁'
            → t₂ [ x := s ]= t₂'
            → app t₁ t₂ [ x := s ]= app t₁' t₂'
  sub-lam₁ : ∀ {t x s}
             → lam x t [ x := s ]= lam x t
  sub-lam₂ : ∀ {x y t s t'}
             → x ≢ y
             → t [ x := s ]= t'
             → lam y t [ x := s ]= lam y t'

lema-1 : ∀ {x t} → ¬ isFV x t
         → ∀ {s} → Σ[ t' ∈ Preterm ] t [ x := s ]= t'
lema-1 {x} {var y}     ¬x∉fvt {s}
  with x ≟ y
...  | yes refl = s , sub-var₁
...  | no  p    = var y , sub-var₂ p
lema-1 {x} {lam y t}   ¬x∉fvt {s}
  with x ≟ y
...  | yes refl = lam x t , sub-lam₁
...  | no  p    =
  let (t' , t[x:=s]=t') = lema-1 {x} {t} (λ { q → ¬x∉fvt (isFV-lam p q) }) {s}
   in lam y t' , sub-lam₂ p t[x:=s]=t'
lema-1 {x} {app t₁ t₂} ¬x∉fvt {s} =
  let (t₁' , t₁[x:=s]=t₁') = lema-1 {x} {t₁} (λ { q → ¬x∉fvt (isFV-app₁ q) }) {s}
      (t₂' , t₂[x:=s]=t₂') = lema-1 {x} {t₂} (λ { q → ¬x∉fvt (isFV-app₂ q) }) {s}
   in app t₁' t₂' , sub-app t₁[x:=s]=t₁' t₂[x:=s]=t₂'

_↔_ : Set → Set → Set
(A ↔ B) = (A → B) × (B → A)

x-not-in-fv-lam-x : ∀ {x t} → ¬ isFV x (lam x t)
x-not-in-fv-lam-x (isFV-lam x≢x _) = x≢x refl

lema-2a : ∀ {t x s t'}
       → t [ x := s ]= t'
       → ∀ {y}
       → (isFV y t' → ((isFV y t × x ≢ y) ⊎ (isFV y s × isFV x t)))
lema-2a sub-var₁               y∈fvs    = inj₂ (y∈fvs , isFV-var)
lema-2a (sub-var₂ {x} {z} x≢z) isFV-var = inj₁ (isFV-var , x≢z)
lema-2a {_} {x} (sub-app t₁[x:=s]=t₁' t₂[x:=s]=t₂') (isFV-app₁ y∈fvt₁')
  with lema-2a t₁[x:=s]=t₁' y∈fvt₁'
... | inj₁ (y∈fvt₁ , x≢y)   = inj₁ (isFV-app₁ y∈fvt₁ , x≢y)
... | inj₂ (y∈fvs , x∈fvt₁) = inj₂ (y∈fvs , isFV-app₁ x∈fvt₁)
lema-2a (sub-app t₁[x:=s]=t₁' t₂[x:=s]=t₂') (isFV-app₂ y∈fvt₂')
  with lema-2a t₂[x:=s]=t₂' y∈fvt₂'
... | inj₁ (y∈fvt₂ , x≢y)   = inj₁ (isFV-app₂ y∈fvt₂ , x≢y)
... | inj₂ (y∈fvs , x∈fvt₂) = inj₂ (y∈fvs , isFV-app₂ x∈fvt₂)
lema-2a {_} {x} sub-lam₁ {y} y∈fvλxt
  with x ≟ y
... | yes refl = ⊥-elim (x-not-in-fv-lam-x y∈fvλxt)
... | no  x≢y  = inj₁ (y∈fvλxt , x≢y)
lema-2a {_} {x} (sub-lam₂ {.x} {z} x≢z t[x:=s]=t') {y} (isFV-lam y≢z y∈fvt')
  with lema-2a t[x:=s]=t' y∈fvt'
... | inj₁ (y∈fvt , x≢y)   = inj₁ (isFV-lam y≢z y∈fvt , x≢y)
... | inj₂ (y∈fvs , x∈fvt) = inj₂ (y∈fvs , isFV-lam x≢z x∈fvt)
