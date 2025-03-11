{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Primitive
open import prelude
open import universal-QIT

-- SK calculus

SK-arity : (Unit ⊕ Unit) ⊕ Unit → List Set
SK-arity (inl _) = []
SK-arity (inr _) = Unit ∷ Unit ∷ []

SK-Sig : Sig
SK-Sig = record { arity = SK-arity }

SK∘ : (Γ : Set) → Set
SK∘ Γ = Tm∘ SK-Sig Γ

S∘ : ∀ {Γ} → SK∘ Γ
S∘ = sym∘ (inl (inl I)) I

K∘ : ∀ {Γ} → SK∘ Γ
K∘ = sym∘ (inl (inr I)) I

app∘ : ∀ {Γ} → SK∘ Γ → SK∘ Γ → SK∘ Γ
app∘ t u = sym∘ (inr I) ((λ _ → t) ,, ((λ _ → u) ,, I))

SK-EqTh : EqTh SK-Sig
SK-EqTh = record {
        E = Unit ⊕ Unit
    ;   Ctx = Ctx'
    ;   lhs = lhs'
    ;   rhs = rhs'
    }
    where
        Ctx' : Unit ⊕ Unit → Set
        Ctx' (inl I) = Unit ⊕ Unit
        Ctx' (inr I) = (Unit ⊕ Unit) ⊕ Unit
        lhs' : (e : Unit ⊕ Unit) → Tm∘ SK-Sig (Ctx' e)
        lhs' (inl I) = app∘ (app∘ K∘ (var∘ (inl I))) (var∘ (inr I))
        lhs' (inr I) = app∘ (app∘ (app∘ S∘ (var∘ (inl (inl I)))) (var∘ (inl (inr I)))) (var∘ (inr I))
        rhs' : (e : Unit ⊕ Unit) → Tm∘ SK-Sig (Ctx' e)
        rhs' (inl I) = var∘ (inl I)
        rhs' (inr I) = app∘ (app∘ (var∘ (inl (inl I))) (var∘ (inr I))) (app∘ (var∘ (inl (inr I))) (var∘ (inr I)))

SK : Set
SK = Tm SK-Sig SK-EqTh

S : SK
S = sym (inl (inl I)) I

K : SK
K = sym (inl (inr I)) I

app : SK → SK → SK
app t u = sym (inr I) ((λ _ → t) ,, ((λ _ → u) ,, I))

K-eq : (x y : SK) → app (app K x) y ≡ x
K-eq x y = eq (inl I) aux
    where
        aux : Unit ⊕ Unit → SK
        aux (inl I) = x
        aux (inr I) = y

S-eq : (x y z : SK) → app (app (app S x) y) z ≡ app (app x z) (app y z)
S-eq x y z = eq (inr I) aux
    where
        aux : (Unit ⊕ Unit) ⊕ Unit → SK
        aux (inl (inl I)) = x
        aux (inl (inr I)) = y
        aux (inr I) = z

record DepSK : Set (lsuc lzero) where
    field
        SK• : SK → Set
        S•  : SK• S
        K•  : SK• K
        app• : {t u : SK} →
                SK• t →
                SK• u →
                SK• (app t u)
        K-eq• : (x y : SK) →
                (x• : SK• x) → (y• : SK• y) →
                app• (app• K• x•) y•
                    ≡ transp (symmetry (cong SK• (K-eq x y)))
                        x•
        S-eq• : (x y z : SK) →
                (x• : SK• x) → (y• : SK• y) → (z• : SK• z) →
                app• (app• (app• S• x•) y•) z•
                    ≡ transp (symmetry (cong SK• (S-eq x y z)))
                        (app• (app• x• z•) (app• y• z•))

mkDepM-SK : DepSK → DepM SK-Sig SK-EqTh
mkDepM-SK M = record {
        Tm•  = λ t → DepSK.SK• M t
    ;   sym• = sym•
    ;   eq•  = eq•
        }
    where
        sym• : (x : (Unit ⊕ Unit) ⊕ Unit) (𝐭 : _) → _ → DepSK.SK• M (sym x 𝐭)
        sym• (inl (inl I)) I I = DepSK.S• M
        sym• (inl (inr I)) I I = DepSK.K• M
        sym• (inr I) (t ,, (u ,, I)) (t• ,, (u• ,, I)) = DepSK.app• M (t• I) (u• I)
        eq• : (e : Unit ⊕ Unit) → (γₑ : _) → (γₑ• : _) → _

        eq• (inl I) γₑ γₑ• = -- with definitional proof irrelevance, this would be
            transp           -- just DepSK.K-eq• M _ _ (γₑ• (inl I)) (γₑ• (inr I))
                (cong ( λ X → (DepSK.app• M (DepSK.app• M (DepSK.K• M) (γₑ• (inl I))) (γₑ• (inr I)))
                    ≡ transp (symmetry (cong (DepSK.SK• M) (X))) (γₑ• (inl I))) Tm-irrel)
                (DepSK.K-eq• M _ _ (γₑ• (inl I)) (γₑ• (inr I)))
        eq• (inr I) γₑ γₑ• = -- with definitional proof irrelevance, this would be
            transp       -- just (DepSK.S-eq• M _ _ _ (γₑ• (inl (inl I))) (γₑ• (inl (inr I))) (γₑ• (inr I)))
                (cong (λ X → (DepSK.app• M (DepSK.app• M (DepSK.app• M (DepSK.S• M) (γₑ• (inl (inl I)))) (γₑ• (inl (inr I)))) (γₑ• (inr I)) ≡ transp (symmetry (cong (DepSK.SK• M) X)) (DepSK.app• M (DepSK.app• M (γₑ• (inl (inl I))) (γₑ• (inr I))) (DepSK.app• M (γₑ• (inl (inr I))) (γₑ• (inr I)))))) Tm-irrel)
                (DepSK.S-eq• M _ _ _ (γₑ• (inl (inl I))) (γₑ• (inl (inr I))) (γₑ• (inr I)))

recSK :  (M : DepSK) →
         (t : SK) →
         DepSK.SK• M t
recSK M t = recTm (mkDepM-SK M) t

recSK-K : ∀ {M} →
    recSK M K
    ≡ DepSK.K• M
recSK-K = refl

recSK-S : ∀ {M} →
    recSK M S
    ≡ DepSK.S• M
recSK-S = refl

recSK-app : ∀ {M x y} →
    recSK M (app x y)
    ≡ DepSK.app• M (recSK M x) (recSK M y)
recSK-app = refl
