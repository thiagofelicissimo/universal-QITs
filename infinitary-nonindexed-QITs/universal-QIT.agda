{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Primitive
open import prelude

record Sig : Set (lsuc lzero) where
    field
        C : Set
        arity : C → List Set


data Tm∘ (Σ : Sig) (Γ : Set) : Set where
    var∘ : Γ → Tm∘ Σ Γ
    sym∘ : (x : Sig.C Σ) → All (λ X → X → Tm∘ Σ Γ) (Sig.arity Σ x) → Tm∘ Σ Γ

record DepM∘ (Σ : Sig) (Γ : Set) : Set (lsuc lzero) where
    field
        Tm∘•  : Tm∘ Σ Γ → Set
        var∘• : (x : Γ) → Tm∘• (var∘ x)
        sym∘• : (x : Sig.C Σ) →
                (𝐭 : All (λ X → X → Tm∘ Σ Γ) (Sig.arity Σ x)) →
                DAll _ (λ X t → (x : X) → Tm∘• (t x)) (Sig.arity Σ x) 𝐭 →
                Tm∘• (sym∘ x 𝐭)


{-# TERMINATING #-}
recTm∘ : ∀ {Σ Γ} →
        (M : DepM∘ Σ Γ) →
        (t : Tm∘ Σ Γ) →
        DepM∘.Tm∘• M t
recTm∘ M (var∘ x) = DepM∘.var∘• M x
recTm∘ M (sym∘ x 𝐭) = DepM∘.sym∘• M x 𝐭 (dall (λ X p x → recTm∘ M (p x)) _ 𝐭)

record EqTh (Σ : Sig) : Set (lsuc lzero) where
    field
        E : Set
        Ctx : E → Set
        lhs : (e : E) → Tm∘ Σ (Ctx e)
        rhs : (e : E) → Tm∘ Σ (Ctx e)


postulate
    Tm : (Σ : Sig) → (𝓔 : EqTh Σ) → Set
    sym : ∀ {Σ 𝓔} → (c : Sig.C Σ) → All (λ X → X → Tm Σ 𝓔) (Sig.arity Σ c) → Tm Σ 𝓔

_⟨_⟩ : ∀ {Σ 𝓔 Γ} → Tm∘ Σ Γ → (Γ → Tm Σ 𝓔) → Tm Σ 𝓔
_⟨_⟩ {Σ} {𝓔} {Γ} t σ = recTm∘ M t
    where   M : DepM∘ Σ Γ
            M = record {
                Tm∘•  = λ _ → Tm Σ 𝓔 ;
                var∘• = λ x → σ x ;
                sym∘• = λ x 𝐭 𝐭• → sym x (transp (symmetry (DAll-const _ _ ((λ X t → (x : X) → Tm Σ 𝓔)) _ 𝐭)) 𝐭•)
                }

postulate
    eq : ∀ {Σ 𝓔} → (e : EqTh.E 𝓔) → (γₑ : EqTh.Ctx 𝓔 e → Tm Σ 𝓔) →
        EqTh.lhs 𝓔 e ⟨ γₑ ⟩ ≡ EqTh.rhs 𝓔 e ⟨ γₑ ⟩


record DepM (Σ : Sig) (𝓔 : EqTh Σ) : Set (lsuc lzero) where
    field
        Tm•  : Tm Σ 𝓔 → Set
        sym• :  (x : Sig.C Σ) →
                (𝐭 : All (λ X → X → Tm Σ 𝓔) (Sig.arity Σ x)) →
                DAll _ (λ X t → (x : X) → Tm• (t x)) (Sig.arity Σ x) 𝐭 →
                Tm• (sym x 𝐭)
        eq• :   (e : EqTh.E 𝓔) →
                (γₑ : EqTh.Ctx 𝓔 e → Tm Σ 𝓔) →
                (γₑ• : (x : EqTh.Ctx 𝓔 e) → Tm• (γₑ x)) →
                let M : DepM∘ Σ (EqTh.Ctx 𝓔 e)
                    -- we interpret tₑ and uₑ according to the methods above
                    M = record {
                            Tm∘•  = λ t → Tm• (t ⟨ γₑ ⟩)
                        ;   var∘• = λ x → γₑ• x
                        ;   sym∘• = λ x 𝐭 𝐭• → transp (cong (λ X → Tm• (sym x X)) (All-map-dall _ _ _ _ _))
                            (sym• x (All-map _ _ (λ X t x → t x ⟨ γₑ ⟩) _ 𝐭) (transp (Dall-map _ _ _ _ _ _) 𝐭•))
                        }
                    p = symmetry (cong Tm• (eq e γₑ))
                in recTm∘ M (EqTh.lhs 𝓔 e) ≡ transp p (recTm∘ M (EqTh.rhs 𝓔 e))


postulate
    recTm : ∀ {Σ 𝓔} →
            (M : DepM Σ 𝓔) →
            (t : Tm Σ 𝓔) →
            DepM.Tm• M t

    rec-sym : ∀ {Σ 𝓔} →
            (M : DepM Σ 𝓔) →
            ∀ {x 𝐭} →
            recTm M (sym x 𝐭) ≡ DepM.sym• M x 𝐭 (dall ((λ X p x → recTm M (p x))) _ 𝐭)

{-# REWRITE rec-sym #-}

postulate
    Tm-irrel : ∀ {Σ 𝓔} → {t u : Tm Σ 𝓔} → {p q : t ≡ u} → p ≡ q
