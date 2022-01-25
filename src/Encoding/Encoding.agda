open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Base as List

import SessionPi as S
import LinearPi as L

infix 4 !_
pattern !_ x = _ , x

-- Encoding of dual session types
-- ⟦ ?A. !B. end ⟧ ≜ chan 1 0 (⟦ A ⟧ × (chan 0 1 (⟦ B ⟧ × chan 0 0 ⊤)))
-- ⟦ !A. ?B. end ⟧ ≜ chan 0 1 (⟦ A ⟧ × (chan 1 0 (⟦ B ⟧ × chan 0 0 ⊤)))

chan<_> : L.Usage × L.Usage × L.Type → L.Type
chan< i , o , t > = L.chan i o t

flip-chan : L.Usage × L.Usage × L.Type → L.Usage × L.Usage × L.Type
flip-chan (i , o , t) = (o , i , t)

mutual
  ⟦_⟧ₑ-type : S.Type → L.Type
  ⟦ S.pure x ⟧ₑ-type = L.pure x
  ⟦ S.chan x ⟧ₑ-type = chan< ⟦ x ⟧ₑ-session >

  ⟦_⟧ₑ-session : S.Session → L.Usage × L.Usage × L.Type
  ⟦ S.end ⟧ₑ-session = L.0∙ , L.0∙ , L.pure ⊤
  ⟦ S.send T C ⟧ₑ-session = L.0∙ , L.1∙ , L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C)
  ⟦ S.recv T C ⟧ₑ-session = L.1∙ , L.0∙ , L.prod ⟦ T ⟧ₑ-type (encode-cont T C)
  ⟦ S.cont T C ⟧ₑ-session = L.0∙ , L.0∙ , L.prod ⟦ T ⟧ₑ-type (encode-cont T C)

  ⟦_⟧ₑ-ctx : S.Ctx → L.Ctx
  ⟦_⟧ₑ-ctx = List.map λ (T , t) → ⟦ T ⟧ₑ-type , encode T t

  decode : ∀ T → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → S.⟦ T ⟧ₜ
  decode (S.pure A) x = x
  decode (S.chan _) _ = tt

  encode : ∀ T → S.⟦ T ⟧ₜ → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ
  encode (S.pure A) x = x
  encode (S.chan _) _ = tt

  encode-cont : (T : S.Type) (C : S.⟦ T ⟧ₜ → S.Session) → (L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → L.Type)
  encode-cont T C = chan<_> ∘ ⟦_⟧ₑ-session ∘ C ∘ decode T

  encode-cont-flip : (T : S.Type) (C : S.⟦ T ⟧ₜ → S.Session) → (L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → L.Type)
  encode-cont-flip T C = chan<_> ∘ flip-chan ∘ ⟦_⟧ₑ-session ∘ C ∘ decode T


flip-dual : ∀ S → ⟦ S.dual S ⟧ₑ-session ≡ flip-chan ⟦ S ⟧ₑ-session
flip-dual S.end = refl
flip-dual (S.recv T C) = cong₂ _,_ refl (cong₂ _,_ refl (cong (L.prod ⟦ T ⟧ₑ-type) {!!}))
flip-dual (S.send T x) = cong₂ _,_ refl (cong₂ _,_ refl (cong (L.prod ⟦ T ⟧ₑ-type) {!!}))
flip-dual (S.cont T x) = cong₂ _,_ refl (cong₂ _,_ refl (cong (L.prod ⟦ T ⟧ₑ-type) refl))

decode-encode : ∀ T {t} → decode T (encode T t) ≡ t
decode-encode (S.pure x) = refl
decode-encode (S.chan x) = refl

postulate ⟦_⟧-null : ∀ {xs : S.Ctx}
                   → S.Null xs
                   → L.Null ⟦ xs ⟧ₑ-ctx

postulate ⟦_⟧-≔-+ : ∀ {xs ys zs}
                  → xs S.≔ ys + zs
                  → ⟦ xs ⟧ₑ-ctx L.≔ ⟦ ys ⟧ₑ-ctx + ⟦ zs ⟧ₑ-ctx

postulate ∋ₜ-exhaust : ∀ {xs n zs T t} → xs S.∋ₜ S.at n (S.exhaust (T , t)) ▹ zs
                     → Σ[ ys ∈ L.Ctx ] ⟦ xs ⟧ₑ-ctx L.≔ ys + ⟦ zs ⟧ₑ-ctx × L.Term ys (⟦ T ⟧ₑ-type , encode T t)

postulate Term-lift : ∀ {x xs t}
                    → L.Null x
                    → L.Term xs t
                    → L.Term (x ∷ xs) t

postulate Process-lift : ∀ {x xs}
                       → L.Null x
                       → L.Process xs
                       → L.Process (x ∷ xs)

∋ₜ-send : ∀ {xs n T C ys zs}
        → xs S.∋ₜ S.at n (S.send T C) ▹ ys
        → ⟦ ys ⟧ₑ-ctx L.[ n ↦ L.chan L.0∙ L.0∙ (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C)), tt ]≔ zs
        → Σ[ ms ∈ L.Ctx ]
          ⟦ xs ⟧ₑ-ctx L.≔ ms + zs
        × L.Term ms (L.chan L.0∙ L.1∙ (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C)) , tt)
∋ₜ-send {_ ∷ xs} (S.here (S.chan S.send)) L.here
  with ! id , null ← L.+-idˡ ⟦ xs ⟧ₑ-ctx
  = ! L.chan L.0∙ L.1∙-left L.∷ id , L.var (L.here null (L.chan L.0∙ L.1∙ refl))
∋ₜ-send {(T , t) ∷ _} (S.there x) (L.there s)
  with ! id , null ← L.+-idˡ (⟦ T ⟧ₑ-type , encode T t)
  = Product.map _ (Product.map (id L.∷_) (Term-lift null)) (∋ₜ-send x s)


mutual
  ⟦_⟧ₚ : ∀ {Γ} → S.Process Γ → L.Process ⟦ Γ ⟧ₑ-ctx
  ⟦ S.end n ⟧ₚ = L.end ⟦ n ⟧-null
  ⟦ S.par s p q ⟧ₚ = L.par ⟦ s ⟧-≔-+ ⟦ p ⟧ₚ ⟦ q ⟧ₚ
  ⟦ S.new S p ⟧ₚ =
    let i , o , t = ⟦ S ⟧ₑ-session in
    let î , ô , t̂ = ⟦ S.dual S ⟧ₑ-session in
    L.new î ô t̂ (L.new i o t ⟦ p ⟧ₚ)
  ⟦ S.rep n p ⟧ₚ = L.rep ⟦ n ⟧-null ⟦ p ⟧ₚ
  ⟦ S.send {T = T} {t = t} {C = C} v s c p ⟧ₚ
    with ci , co , ct ← ⟦ C t ⟧ₑ-session in eq
    with Δ , spv , tv ← ∋ₜ-exhaust v
    with ! spc , tc ← ∋ₜ-send s {!!}
    with ! spp , np ← L.+-idʳ Δ
    with a , t-right , t-nleft ← L.+-idˡ (L.chan ci co ct , tt)
    with b , t̂-left , t̂-nright ← L.+-idʳ (L.chan co ci ct , tt)
    with ! t̂-right , t̂-nleft ← L.+-idˡ (L.chan co ci ct , tt)
    with ! a-right , a-nleft ← L.+-idˡ a
    with ! b-right , b-nleft ← L.+-idˡ b
    with ! Δ-left , Δ-null ← L.+-idʳ Δ
    = L.new ci co ct
    $ L.new co ci ct
    $ L.send
      (t̂-left L.∷ t-right  L.∷ spv)
      (L.pair (t̂-right L.∷ a-right L.∷ Δ-left)
              (Term-lift t̂-nleft (Term-lift a-nleft tv))
              (L.var (L.here (t-nleft L.∷ Δ-null) (L.chan
                (subst (λ ● → proj₁ (proj₂ (⟦ C ● ⟧ₑ-session)) L.⊆ co) (sym (decode-encode T {t})) (subst (L._⊆ co) (cong (proj₁ ∘ proj₂) (sym eq)) (L.⊆-refl _)))
                (subst (λ ● → proj₁ (⟦ C ● ⟧ₑ-session) L.⊆ ci)         (sym (decode-encode T {t})) (subst (L._⊆ ci) (cong (proj₁)         (sym eq)) (L.⊆-refl _)))
                (trans (cong (λ ● → proj₂ (proj₂ ⟦ C ● ⟧ₑ-session)) (decode-encode T {t})) (cong (proj₂ ∘ proj₂) eq))))))
      (b-right L.∷ t-right L.∷ spc)
      (Term-lift b-nleft (Term-lift t-nleft tc))
      (Process-lift t̂-nright {!⟦ p ⟧ₚ!})
  ⟦ S.recv s p ⟧ₚ
    = L.recv {!!} {!!} λ t → {!p t!}
