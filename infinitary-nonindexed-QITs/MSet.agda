{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Primitive
open import prelude
open import universal-QIT

-- Finite Multisets

MSet-arity : (A : Set) → Unit ⊕ A → List Set
MSet-arity A (inl _) = []
MSet-arity A (inr _) = Unit ∷ []

MSetSig : (A : Set) → Sig
MSetSig A = record { C = Unit ⊕ A ; arity = MSet-arity A}

MSet∘ : (A Γ : Set) → Set
MSet∘ A Γ = Tm∘ (MSetSig A) Γ

nil∘ : ∀ {A Γ} → MSet∘ A Γ
nil∘ = sym∘ (inl I) I

cons∘ : ∀ {A Γ} → A → MSet∘ A Γ → MSet∘ A Γ
cons∘ x m = sym∘ (inr x) ((λ _ → m) ,, I)

MSetEqTh : (A : Set) → EqTh (MSetSig A)
MSetEqTh A = record {
        E = A × A
    ;   Ctx = λ _ → Unit
    ;   lhs = λ e → cons∘ (_×_.fst e) (cons∘ (_×_.snd e) (var∘ I))
    ;   rhs = λ e → cons∘ (_×_.snd e) (cons∘ (_×_.fst e) (var∘ I))
    }

MSet : (A : Set) → Set
MSet A = Tm (MSetSig A) (MSetEqTh A)

nil : ∀ {A} → MSet A
nil = sym (inl I) I

cons : ∀ {A} → A → MSet A → MSet A
cons x m = sym (inr x) ((λ _ → m) ,, I)

cons-cons-eq : ∀ {A} → (x y : A) → (m : MSet A) → cons x (cons y m) ≡ cons y (cons x m)
cons-cons-eq x y m = eq (x ,, y) λ _ → m

record DepMSet (A : Set) : Set (lsuc lzero) where
    field
        MSet• : MSet A → Set
        nil•  : MSet• nil
        cons• : (x : A) →
                (m : MSet A) →
                MSet• m →
                MSet• (cons x m)
        cons-cons• :    (x y : A) →
                        (m : MSet A) →
                        (m• : MSet• m) →
                        cons• x _ (cons• y _ m•)
                            ≡ transp (symmetry (cong MSet• (cons-cons-eq x y m)))
                            (cons• y _ (cons• x _ m•))

mkDepM-MSet : ∀ {A} → DepMSet A → DepM (MSetSig A) (MSetEqTh A)
mkDepM-MSet {A} M = record {
        Tm•  = λ t → DepMSet.MSet• M t
    ;   sym• =  sym•
    ;   eq•  = λ x γₑ γₑ• → DepMSet.cons-cons• M (_×_.fst x) (_×_.snd x)  (γₑ I) (γₑ• I)
        }
    where   sym• :  (x : Unit ⊕ A)
                    (𝐭 : _) →
                    (𝐭• : _) →
                    DepMSet.MSet• M (sym x 𝐭)
            sym• (inl I) I I                = DepMSet.nil• M
            sym• (inr x) (m ,, I) (m• ,, I) = DepMSet.cons• M x (m I) (m• I)

recMSet : ∀ {A} →
            (M : DepMSet A) →
            (t : MSet A) →
            DepMSet.MSet• M t
recMSet M t = recTm (mkDepM-MSet M) t

recMSet-nil : ∀ {A M} →
    recMSet {A} M nil
    ≡ DepMSet.nil• M
recMSet-nil = refl

recMSet-cons : ∀ {A M x m} →
    recMSet {A} M (cons x m)
    ≡ DepMSet.cons• M x m (recMSet M m)
recMSet-cons = refl