open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Primitive

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,,_
  field
    fst : A
    snd : B fst

record _×_ {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  constructor _,,_
  field
    fst : A
    snd : B

record Unit {i} : Set i where
    constructor I

Vec : (A : Set) → Nat → Set
Vec A zero    = Unit
Vec A (suc n) = A × Vec A n


data _⊕_ (A B : Set) : Set where
   inl : A → A ⊕ B
   inr : B → A ⊕ B

subst : ∀ {l} → {A : Set} {a b : A} (F : A → Set l) → a ≡ b → F a → F b
subst F refl f = f

subst₂ : ∀ {l} →{A B : Set} {a a' : A} {b b' : B} (F : A → B → Set l) → a ≡ a' → b ≡ b' → F a b → F a' b'
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

All : ∀ {i j}{A : Set i} → (P : A → Set j) → List A → Set j
All P []  = Unit
All P (x ∷ l) = P x × (All P l)

All-map : ∀ {i j j'} {A : Set i} → (P : A → Set j) → (P' : A → Set j') →
            (f : (x : A) → P x → P' x) →
            (l : List A) → All P l → All P' l
All-map P P' f [] I = I
All-map P P' f (x ∷ l) (px ,, pl) = f x px ,, All-map P P' f l pl

all : ∀ {i j} {A : Set i} → (P : A → Set j) → (p : (x : A) → P x) → (l : List A) → All P l
all P p [] = I
all P p (x ∷ l) = p x ,, (all P p l)

map : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → List A → List B
map f [] = []
map f (x ∷ l) = (f x) ∷ (map f l)


DAll : ∀ {i j j'}{A : Set i} → (P : A → Set j) → (F : (x : A) → P x → Set j') →
        (l : List A) → All P l → Set j'
DAll P F [] I = Unit
DAll P F (x ∷ l) (px ,, pl) = F x px × DAll P F l pl

DAll-const : ∀ {i j j' k}{A : Set i} → (P : A → Set j) → (P' : A → Set j') → (F : (x : A) → P x → Set k) →
        (l : List A) → (pl : All P l) →
        All P' l ≡ DAll P (λ x px → P' x) l pl
DAll-const P P' F [] _ = refl
DAll-const P P' F (x ∷ l) (_ ,, pl) = cong (λ X → _ × X) (DAll-const P P' F l pl)

dall : ∀ {i j j'}{A : Set i} → {P : A → Set j} → {F : (x : A) → P x → Set j'} →
        (f : (x : A) → (p : P x) → F x p) →
        (l : List A) → (pl : All P l) → DAll P F l pl
dall f [] I = I
dall f (x ∷ l) (px ,, pl) = f x px ,, dall f l pl


transp× :   ∀ {i} {A B B' : Set i} →
            {a : A} → {p : B ≡ B'}  →
            {b : B} {b' : B'} →
            b ≡ transp (symmetry p) b' →
            (a ,, b) ≡ transp (symmetry (cong (λ X → A × X) p)) (a ,, b')
transp× {p = refl} refl = refl


All-map-dall : ∀ {i j j'}{A : Set i} → (P : A → Set j) → (P' : A → Set j') →
            (f : (x : A) → P x → P' x) → (l : List A) → (pl : All P l) →
            All-map P P' f l pl ≡ transp (symmetry (DAll-const P P' (λ x _ → P x) l pl)) (dall f l pl)
All-map-dall P P' f [] I = refl
All-map-dall P P' f (x ∷ l) (px ,, pl) = transp× (All-map-dall P P' f l pl)


Dall-map : ∀ {i j j' k}{A : Set i} → (P : A → Set j) → (P' : A → Set j') →
        (f : (x : A) → P x → P' x) → (G : (x : A) → P' x → Set k) →
        (l : List A) → (pl : All P l) → DAll _ (λ x px → G _ (f x px)) l pl ≡ DAll P' G l (All-map P P' f l pl)
Dall-map P P' f G [] pl = refl
Dall-map P P' f G (x ∷ l) (px ,, pl) = cong (λ X → _ × X) (Dall-map P P' f G l pl)
