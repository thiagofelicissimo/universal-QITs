open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Primitive


record _×_ {i} (A B : Set i) : Set i where
  constructor _,,_
  field
    fst : A
    snd : B

record Unit : Set where
    constructor I

Vec : (A : Set) → Nat → Set
Vec A zero    = Unit
Vec A (suc n) = A × Vec A n

data _⊕_ (A B : Set) : Set where
   inl : A → A ⊕ B
   inr : B → A ⊕ B



subst : {A : Set} {a b : A} {ℓ : Agda.Primitive.Level} (F : A → Set ℓ) → a ≡ b → F a → F b
subst F refl f = f

subst₂ : {A B : Set} {a a' : A} {b b' : B} {ℓ : Agda.Primitive.Level} (F : A → B → Set ℓ) → a ≡ a' → b ≡ b' → F a b → F a' b'
subst₂ F refl refl f = f

cong : ∀ {l l'} {A : Set l} {B : Set l'} {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl


cong₂ : ∀ {l l' l''} {A : Set l} {B : Set l'} {C : Set l''} {a a′ b b′}
        (f : A → B → C) → a ≡ a′ → b ≡ b′
      → f a b ≡ f a′ b′
cong₂ f refl refl = refl

cong₃ : ∀ {A B C D : Set} {a a' b b' c c'}
        (f : A → B → C → D) → a ≡ a' → b ≡ b' → c ≡ c'
      → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl


symmetry : ∀ {i} {A : Set i} {a b : A} → a ≡ b → b ≡ a
symmetry refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl p = p

transp : ∀ {i} {A B : Set i} → A ≡ B → A → B
transp refl a = a


All : ∀ {A} → (P : A → Set) → (n : Nat) → Vec A n → Set
All P zero I  = Unit
All P (suc n) (x ,, l) = P x × (All P n l)

all : ∀ {A} → (P : A → Set) → (p : (x : A) → P x) → (n : Nat) → (l : Vec A n) → All P n l
all P p zero I = I
all P p (suc n) (x ,, l) = p x ,, (all P p n l)

map : ∀ {A B} → (f : A → B) → (n : Nat) → Vec A n → Vec B n
map f zero I = I
map f (suc n) (x ,, l) = (f x) ,, (map f n l)

All-map : ∀ {A B} {f : A → B} {P n} → (l : Vec A n) → All (λ x → P (f x)) n l ≡ All P n (map f n l)
All-map {n = zero} I = refl
All-map {n = suc m} (x ,, l) = cong (λ X → _ × X) (All-map {n = m} l)

All-const : ∀ {A B} → (n : Nat) → (l : Vec A n) → All (λ _ → B) n l ≡ Vec B n
All-const zero I = refl
All-const (suc n) (x ,, l) = cong (λ X → _ × X) (All-const n l)

transp× :   ∀ {A B B' : Set} →
            {a : A} → {p : B' ≡ B}  →
            {b : B} {b' : B'} →
            b ≡ transp p b' →
            (a ,, b) ≡ transp (cong (λ X → A × X) p) (a ,, b')
transp× {p = refl} refl = refl

all-map : ∀ {A B} → (n : Nat) → (l : Vec A n) → (f : A → B) → map f n l ≡ transp (All-const n l) (all (λ _ → B) f n l)
all-map zero I f = refl
all-map (suc n) (x ,, l) f = transp× (all-map n l f)