{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Primitive
open import prelude
open import universal-QIT

-- Unordered countably-branching trees

CTree-arity : Unit ⊕ Unit → List Set
CTree-arity (inl _) = []
CTree-arity (inr _) = Nat ∷ []

CTreeSig : Sig
CTreeSig = record { C = Unit ⊕ Unit ; arity = CTree-arity}

CTree∘ : (Γ : Set) → Set
CTree∘ Γ = Tm∘ CTreeSig Γ

leaf∘ : ∀ {Γ} → CTree∘ Γ
leaf∘ = sym∘ (inl _) I

node∘ : ∀ {Γ} → (Nat → CTree∘ Γ) → CTree∘ Γ
node∘ f = sym∘ (inr _) (f ,, I)

isBij : (Nat → Nat) → Set
isBij f = Σ (Nat → Nat) (λ g →
            ((x : Nat) → f (g x) ≡ x) ×
            ((x : Nat) → g (f x) ≡ x))

CTreeEqTh : EqTh CTreeSig
CTreeEqTh = record {
        E = Σ (Nat → Nat) (λ f → isBij f)
    ;   Ctx = λ _ → Nat
    ;   lhs = λ g → node∘ (λ x → var∘ x)
    ;   rhs = λ g → node∘ (λ x → var∘ (Σ.fst g x))
    }

CTree : Set
CTree = Tm CTreeSig CTreeEqTh

leaf : CTree
leaf = sym (inl _) I

node : (Nat → CTree) → CTree
node f = sym (inr _) (f ,, I)


node-comp : (g : Nat → Nat) → isBij g → (f : Nat → CTree) → node f ≡ node (λ x → f (g x))
node-comp g p f = eq (g ,, p) λ x → f x

record DepCTree : Set (lsuc lzero) where
    field
        CTree• : CTree → Set
        leaf•  : CTree• leaf
        node•  : (t : Nat → CTree) →
                ((n : Nat) → CTree• (t n)) →
                CTree• (node t)
        cons-cons• :    (g : Nat → Nat) →
                        (p : isBij g) →
                        (f : Nat → CTree) →
                        (f• : (n : Nat) → CTree• (f n)) →
                        node• f f• ≡
                            transp (symmetry (cong CTree• (node-comp g p f)))
                                (node• (λ x → f (g x)) λ x → f• (g x))



mkDepM-CTree : DepCTree → DepM CTreeSig CTreeEqTh
mkDepM-CTree M = record {
        Tm•  = λ t → DepCTree.CTree• M t
    ;   sym• = sym•
    ;   eq•  = λ e γₑ γₑ• → DepCTree.cons-cons• M (Σ.fst e) (Σ.snd e) γₑ γₑ•
        }
    where
        sym• :  (x : Unit ⊕ Unit) →
                (𝐭 : All (λ X → X → Tm CTreeSig CTreeEqTh) (CTree-arity x)) →
                DAll (λ X → X → Tm CTreeSig CTreeEqTh) (λ X t → (x₁ : X) → DepCTree.CTree• M (t x₁)) (CTree-arity x) 𝐭 → DepCTree.CTree• M (sym x 𝐭)
        sym• (inl _) I I = DepCTree.leaf• M
        sym• (inr _) (f ,, I) (f• ,, I) = DepCTree.node• M f f•


recCTree :  (M : DepCTree) →
            (t : CTree) →
            DepCTree.CTree• M t
recCTree M t = recTm (mkDepM-CTree M) t

recCTree-leaf : ∀ {M} →
    recCTree M leaf
    ≡ DepCTree.leaf• M
recCTree-leaf = refl

recCTree-node : ∀ {M f} →
    recCTree M (node f)
    ≡ DepCTree.node• M f λ x → recCTree M (f x)
recCTree-node = refl
