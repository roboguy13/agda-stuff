open import Level
open import Category
open import FunctorDefs hiding (Σ![_⇒_])

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

module ElementaryProperties
  {o : Level}
  {ℓ : Level}
  (ℂ : Category o ℓ)
  where

open Category.Category ℂ
open CatBasics ℂ

private
  Σ![_⇒_] : ∀ {m} (A B : Obj) → ((A ⇒ B) → Set m) → Set (ℓ ⊔ m)
  Σ![_⇒_] A B P = Σ![ A ⇒[ ℂ ] B ] P

IsProduct : ∀   A B A×B → Set (o ⊔ ℓ)
IsProduct    A B A×B =
  ∃[ p ] ∃[ q ] (∀ {X} (f : X ⇒[ ℂ ] A) (g : X ⇒[ ℂ ] B) →
              Σ![ X ⇒[ ℂ ] A×B ] λ m → (f ≡ (p ∘[ ℂ ] m)) × (g ≡ (q ∘[ ℂ ] m)))


-- -- Σ![[_]] : 

IsTerminal : ∀ (T : Obj) → Set (o ⊔ ℓ)
IsTerminal T = ∀ A → Σ![ A ⇒ T ] λ _ → ⊤
-- IsTerminal T = ∀ {A} {f g : A ⇒ T} → f ≈ g

IsInitial : ∀ (I : Obj) → Set (o ⊔ ℓ)
IsInitial I = ∀ B → Σ![ I ⇒ B ] λ _ → ⊤
-- IsInitial I = ∀ {B} {f g : I ⇒ B} → f ≈ g

𝟙-map : ∀ {𝟙} → IsTerminal 𝟙 → ∀ {A} → (A ⇒ 𝟙)
𝟙-map prf {A} = proj₁ (prf A)

𝟘-map : ∀ {𝟘} → IsInitial 𝟘 → ∀ {A} → (𝟘 ⇒ A)
𝟘-map prf {A} = proj₁ (prf A)

product-proj₁ : ∀ {A B A×B} →
  IsProduct A B A×B →
  (A×B) ⇒ A
product-proj₁ (p , _) = p

product-proj₂ : ∀ {A B A×B} →
  IsProduct A B A×B →
  (A×B) ⇒ B
product-proj₂ (_ , q , _) = q

IsCoproduct : ∀ A B A+B → Set (o ⊔ ℓ)
IsCoproduct A B A+B =
  ∃[ i ] ∃[ j ] (∀ {X} (f : A ⇒ X) (g : B ⇒ X) →
              Σ![ A+B ⇒ X ] λ m → (f ≡ (m ∘ i)) × (g ≡ (m ∘ j)))

coproduct-inj₁ : ∀ {A B A+B} →
  IsCoproduct A B A+B →
  A ⇒ (A+B)
coproduct-inj₁ (i , _) = i

coproduct-inj₂ : ∀ {A B A+B} →
  IsCoproduct A B A+B →
  B ⇒ (A+B)
coproduct-inj₂ (_ , j , _) = j

IsSeparator : ∀ (S : Obj) → Set (o ⊔ ℓ)
IsSeparator S = ∀ {X Y} {f₁ f₂ : X ⇒ Y} →
  ((∀ (x : S ⇒ X) → (f₁ ∘ x) ≡ (f₂ ∘ x))) → f₁ ≡ f₂

IsCoseparator : ∀ (V : Obj) → Set (o ⊔ ℓ)
IsCoseparator V = ∀ {T A} {a₀ a₁ : T ⇒ A} →
  ((∀ (φ : A ⇒ V) → (φ ∘ a₀) ≡ (φ ∘ a₁))) → a₀ ≡ a₁

Coseparate-contra : ∀ {V : Obj} → IsCoseparator V →
  ∀ {T} {A} {a₀ a₁ : T ⇒ A} →
  ¬ (a₀ ≡ a₁) → ¬ (∀ (φ : A ⇒ V) → (φ ∘ a₀) ≡ (φ ∘ a₁))
Coseparate-contra cosep {T} {A} {a₀} {a₁} ref prf = ref (cosep prf)

Monic : ∀ {A B} → (A ⇒ B) → Set (o ⊔ ℓ)
Monic {A} {B} f =
  ∀ X (g₁ g₂ : X ⇒ A) →
    ((f ∘ g₁) ≡ (f ∘ g₂)) → (g₁ ≡ g₂)

Epic : ∀ {A B} → (A ⇒ B) → Set (o ⊔ ℓ)
Epic {A} {B} f =
  ∀ Y (g₁ g₂ : B ⇒ Y) →
    ((g₁ ∘ f) ≡ (g₂ ∘ f)) → (g₁ ≡ g₂)

_↣_ : ∀ (A B : Obj) → Set (o ⊔ ℓ)
A ↣ B = Σ (A ⇒ B) Monic

_↠_ : ∀ (A B : Obj) → Set (o ⊔ ℓ)
A ↠ B = Σ (A ⇒ B) Epic

Retraction : ∀ {A B} (i : A ⇒ B) (r : B ⇒ A) → Set ℓ
Retraction {A} {B} i r = (r ∘ i) ≡ id {A}

Retract : ∀ (A B : Obj) → Set ℓ
Retract A B = ∃[ i ] ∃[ r ] (Retraction {A} {B} i r)

!Retract : ∀ (A B : Obj) → Set ℓ
!Retract A B =
  ∃[ i ] ∃[ r ]
    (Retraction {A} {B} i r
      ×
      ((i′ : A ⇒ B) → (r′ : B ⇒ A) → (Retraction i′ r′) →
        (i′ ≡ i) × (r′ ≡ r)))


∃_[_,,_]_ : ∀ {m} (R : ∀ X Y → Set m) (A B : Obj) →
  (P : R A B → Set m) → Set m
∃ R [ A ,, B ] P =
  Σ (R A B) P

𝟙⇒𝟙-is-id : ∀ {𝟙} → IsTerminal 𝟙 → (f : 𝟙 ⇒ 𝟙) → f ≡ id
𝟙⇒𝟙-is-id {𝟙} 𝟙-terminal f with 𝟙-terminal 𝟙
... | fst , fst₁ , snd =
        let eq1 = snd f tt
            eq2 = snd id tt
        in
        trans eq1 (sym eq2)

𝟘⇒𝟘-is-id : ∀ {𝟘} → IsInitial 𝟘 → (f : 𝟘 ⇒ 𝟘) → f ≡ id
𝟘⇒𝟘-is-id {𝟘} 𝟘-initial f with 𝟘-initial 𝟘
... | fst , fst₁ , snd =
        let eq1 = snd f tt
            eq2 = snd id tt
        in
        trans eq1 (sym eq2)

𝟙-map-unique : ∀ {𝟙} → (𝟙-terminal : IsTerminal 𝟙) →
  ∀ {A} →
  {f g : A ⇒ 𝟙} →
  f ≡ 𝟙-map 𝟙-terminal {A}
𝟙-map-unique 𝟙-terminal {A} {f} with 𝟙-terminal A
... | x , y , z = z f tt

𝟘-map-unique : ∀ {𝟘} → (𝟘-initial : IsInitial 𝟘) →
  ∀ {A} →
  {f : 𝟘 ⇒ A} →
  f ≡ 𝟘-map 𝟘-initial {A}
𝟘-map-unique 𝟘-initial {A} {f} with 𝟘-initial A
... | x , y , z = z f tt

𝟙-maps-same : ∀ {𝟙} → (𝟙-terminal : IsTerminal 𝟙) →
  ∀ {A} →
  {f g : A ⇒ 𝟙} →
  f ≡ g
𝟙-maps-same {𝟙} 𝟙-terminal {A} {f} {g} with 𝟙-terminal A
... | x , y , z =
  let
    p = z f tt
    q = z g tt
  in
  trans p (sym q)

𝟘-maps-same : ∀ {𝟘} → (𝟘-initial : IsInitial 𝟘) →
  ∀ {A} →
  {f g : 𝟘 ⇒ A} →
  f ≡ g
𝟘-maps-same {𝟘} 𝟘-initial {A} {f} {g} with 𝟘-initial A
... | x , y , z =
  let
    p = z f tt
    q = z g tt
  in
  trans p (sym q)

Iso : ∀ {A B} (f : A ⇒ B) (g : B ⇒ A) → Set ℓ
Iso f g = Retraction f g × Retraction g f

!Iso : ∀ {A B} (f : A ⇒ B) (g : B ⇒ A) → Set ℓ
!Iso {A} {B} f g =
  Iso f g × ((f′ : A ⇒ B) → (g′ : B ⇒ A) → (Iso {A} {B} f′ g′) →
    ((f′ ≡ f) × (g′ ≡ g)))

_≅_ : ∀ (A B : Obj) → Set ℓ
A ≅ B = ∃[ f ] ∃[ g ] (Iso {A} {B} f g)

Is-Iso : ∀ (A B : Obj) → Set ℓ
Is-Iso A B = A ≅ B

Is-!Iso : ∀ (A B : Obj) → Set ℓ
Is-!Iso A B = ∃[ f ] ∃[ g ] !Iso {A} {B} f g

ΣIso[_⇒_]_ : ∀ A B → (∀ f g → Iso {A} {B} f g → Set ℓ) → Set ℓ
ΣIso[ A ⇒ B ] P =
  ∃[ f ] ∃[ g ] (Σ (Iso f g) (P f g))

Σ!Iso[_⇒_] : ∀ A B → (∀ f g → Iso {A} {B} f g → Set ℓ) → Set ℓ
Σ!Iso[ A ⇒ B ] P =
  ΣIso[ A ⇒ B ] λ f g i →
    ∀ f′ g′ →
    Iso f′ g′ →
    (f′ ≡ f) × (g′ ≡ g)

Strict-Initial : ∀ {𝟘 : Obj} →
  IsInitial 𝟘 →
  Set (o ⊔ ℓ)
Strict-Initial {𝟘} 𝟘-initial =
  ∀ {A} (f : A ⇒ 𝟘) →
  Iso f (𝟘-map 𝟘-initial)

Nondegenerate : ∀ {𝟙 𝟘 : Obj} → IsTerminal 𝟙 → IsInitial 𝟘 → Set ℓ
Nondegenerate {𝟙} {𝟘} _ _ = ¬ (𝟙 ≅ 𝟘)

Nondegenerate′ : ∀ {𝟙 : Obj} → IsTerminal 𝟙 → Set (o ⊔ ℓ)
Nondegenerate′ {𝟙} _ = ¬ IsInitial 𝟙

Nondegenerate→no-𝟙⇒𝟘 : ∀ {𝟙 𝟘 : Obj} →
  (𝟙-terminal : IsTerminal 𝟙) →
  (𝟘-initial : IsInitial 𝟘) →
  Nondegenerate 𝟙-terminal 𝟘-initial →
  ¬ (𝟙 ⇒ 𝟘)
Nondegenerate→no-𝟙⇒𝟘 {𝟙} {𝟘} 𝟙-terminal 𝟘-initial nondegen 𝟙⇒𝟘 =
  let
    p : 𝟙 ⇒ 𝟙
    p = 𝟙-map 𝟙-terminal ∘ 𝟙⇒𝟘

    q : 𝟘 ⇒ 𝟘
    q = 𝟙⇒𝟘 ∘ 𝟙-map 𝟙-terminal

    eq1 : p ≡ id
    eq1 = 𝟙⇒𝟙-is-id 𝟙-terminal p

    eq2 : q ≡ id
    eq2 = 𝟘⇒𝟘-is-id 𝟘-initial q
  in
  nondegen (𝟙⇒𝟘 , (𝟙-map 𝟙-terminal , (eq1 , eq2)))

-- unique-retract→iso : ∀ {A B} →
--   !Retract A B →
--   A ≅ B
-- unique-retract→iso {A} {B} !retract =
--   let
--     retract , unique = !retract
--   in
--   {!!}

retract-retract→iso : ∀ {A} {B} {f g h} →
  Retraction {A} {B} f g →
  Retraction {B} {A} g h →
  A ≅ B
retract-retract→iso {A} {B} {f} {g} {h} retract-f-g retract-g-h =
  let
    z : (g ∘ f) ≡ id
    z = retract-f-g

    w : (h ∘ g) ≡ id
    w = retract-g-h

    r1 : (f ∘ g) ≡ ((h ∘ g) ∘ (f ∘ g))
    r1 = trans (sym left-id) (postcomp-≡ (sym retract-g-h))

    r2′ : ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
    r2′ = ∘-assoc

    r2′′ : ((h ∘ g) ∘ (f ∘ g)) ≡ (h ∘ ((g ∘ f) ∘ g))
    r2′′ = trans ∘-assoc4 (rewrite-right-∘ ∘-assoc refl)

    r2 : (f ∘ g) ≡ (h ∘ ((g ∘ f) ∘ g))
    r2 = trans r1 r2′′

    r3′ : (h ∘ ((g ∘ f) ∘ g)) ≡ ((h ∘ (g ∘ f)) ∘ g)
    r3′ = sym ∘-assoc

    r3′′ : (f ∘ g) ≡ ((h ∘ (g ∘ f)) ∘ g)
    r3′′ = trans r2 r3′

    hgfg≡g : ((h ∘ (g ∘ f)) ∘ g) ≡ (h ∘ g)
    hgfg≡g = rewrite-left-∘ (rewrite-right-∘ retract-f-g refl) (rewrite-left-∘ (sym right-id) refl)

    r3 : (f ∘ g) ≡ (h ∘ g)
    r3 = trans r3′′ (rewrite-right-∘ refl hgfg≡g)

    r : (f ∘ g) ≡ id
    r = trans r3 retract-g-h
  in
  f , g , retract-f-g , r

--      p2
--    P -> B
-- p1 |    | g
--    v    v
--    A -> X
--      f

CSquare : ∀ {A B X P} (f : A ⇒ X) (g : B ⇒ X)
  (p₁ : P ⇒ A) (p₂ : P ⇒ B) → Set ℓ
CSquare f g p₁ p₂ =
  (f ∘ p₁) ≡ (g ∘ p₂)

IsPullback : ∀ A B X (f : A ⇒ X) (g : B ⇒ X) →
  (P : Obj) → (P ⇒ A) → (P ⇒ B) → Set (o ⊔ ℓ)
IsPullback A B X f g P p₁ p₂ =
  CSquare f g p₁ p₂ ×
    ∀ Z f′ g′ p₁′ p₂′ →
    CSquare {A} {B} {X} {Z} f′ g′ p₁′ p₂′ →
    (Σ![ Z ⇒ P ] λ m →
      ((p₁ ∘ m) ≡ p₁′)
        ×
      ((p₂ ∘ m) ≡ p₂′))


--      !
--   A --> 𝟙
--   v     |
-- f |     | true
--   v     v
--   B --> Ω
--      χ

Subobj-Classify : ∀ {𝟙 Ω} → (𝟙-term : IsTerminal 𝟙) →
  (tr : 𝟙 ⇒ Ω) → Set (o ⊔ ℓ)
Subobj-Classify {𝟙} {Ω} 𝟙-term tr =
  ∀ {A B} {f : A ⇒ B} → Monic f →
  Σ![ B ⇒ Ω ] λ χ →
    IsPullback B 𝟙 Ω χ tr A f (𝟙-map 𝟙-term {A})



Boolean : ∀ {𝟙} → (𝟙-term : IsTerminal 𝟙) →
  ∀ {Ω} → (tr : 𝟙 ⇒ Ω) → Subobj-Classify 𝟙-term tr →
  ∀ {𝟙+𝟙 : Obj} → IsCoproduct 𝟙 𝟙 𝟙+𝟙 →
  Set ℓ
Boolean {_} _ {Ω} _ _ {𝟙+𝟙} _ = Ω ≅ 𝟙+𝟙

Terminal-unique-Iso : ∀ {A} →
  IsTerminal A →
  ∀ {X} → IsTerminal X →
  Σ!Iso[ X ⇒ A ] (λ _ _ _ → Lift ℓ ⊤)
Terminal-unique-Iso {A} A-term {X} X-term with A-term X in eq₁ | X-term A in eq₂
... | fst , fst₂ , snd | fst₁ , fst₃ , snd₁ =
  let
    s₁ , s₂ , s₃ = A-term A
    t₁ , t₂ , t₃ = X-term X

    m = t₃ (proj₁ (X-term A) ∘ proj₁ (A-term X)) tt
    m′ = t₃ id tt

    n = s₃ (proj₁ (A-term X) ∘ proj₁ (X-term A)) tt
    n′ = s₃ id tt

    z : (proj₁ (X-term A) ∘ proj₁ (A-term X)) ≡ id {X}
    z = trans m (sym m′)

    w : (proj₁ (A-term X) ∘ proj₁ (X-term A) ) ≡ id {A}
    w = trans n (sym n′)
  in
  proj₁ (A-term X) ,
  proj₁ (X-term A) ,
  (z , w) ,
  λ f′ g′ x → proj₂ (proj₂ (A-term X)) f′ tt ,
  proj₂ (proj₂ (X-term A)) g′ tt

point-monic : ∀ {𝟙} → IsTerminal 𝟙 →
  ∀ {A} →
  (f : 𝟙 ⇒ A) →
  Monic f
point-monic prf {A} f X g h eq with prf X
... | fst , fst₁ , snd =
  let p = snd g tt
      q = snd h tt
  in
  trans p (sym q)

bimap :
  (_⊗_ : Obj → Obj → Obj) →
  (∀ X Y → IsProduct X Y (X ⊗ Y)) →
  ∀ {A A′ B B′} (f : A ⇒ A′) (g : B ⇒ B′) →
  (A ⊗ B) ⇒ (A′ ⊗ B′)
bimap _⊗_ product {A} {A′} {B} {B′} f g =
  let
    p₁ : (A ⊗ B) ⇒ A
    p₁ = product-proj₁ (product A B)

    p₂ : (A ⊗ B) ⇒ B
    p₂ = product-proj₂ (product A B)

    s : (A ⊗ B) ⇒ A′
    s = f ∘ p₁

    t : (A ⊗ B) ⇒ B′
    t = g ∘ p₂

    _ , _ , pair-map = product A′ B′

    m , _ , _ = pair-map {A ⊗ B} s t
  in
  m

diagonal :
  (_⊗_ : Obj → Obj → Obj) →
  (∀ X Y → IsProduct X Y (X ⊗ Y)) →
  ∀ {A} →
  A ⇒ (A ⊗ A)
diagonal _⊗_ product {A} with product A A
... | x , y , z =
  let t1 , t2 = z {A} id id
  in
  t1

joined-bimap :
  (_⊗_ : Obj → Obj → Obj) →
  (∀ X Y → IsProduct X Y (X ⊗ Y)) →
  ∀ {Z A B} (f : Z ⇒ A) (g : Z ⇒ B) →
  Z ⇒ (A ⊗ B)
joined-bimap _⊗_ product f g =
  bimap _⊗_ product f g ∘ diagonal _⊗_ product

bimap-id :
  (_⊗_ : Obj → Obj → Obj) →
  (product : ∀ X Y → IsProduct X Y (X ⊗ Y)) →
  ∀ {A B} →
  bimap _⊗_ product {A} {A} {B} {B} id id ≡ id
bimap-id _⊗_ product {A} {B} =
  let
    fst , fst₁ , snd = product A B
    fst₂ , (u , v) , snd₁ = snd fst fst₁
    p : id ≡ fst₂
    p = snd₁ id (sym right-id , sym right-id)

    x , (y , z) , w = snd (product-proj₁ (product A B)) (product-proj₂ (product A B))

    prf : product-proj₁ (product A B) ≡ fst
    prf = refl

    prf2 : product-proj₂ (product A B) ≡ fst₁
    prf2 = refl

    prf3′ : proj₁ (proj₂ (product A B)) ≡ fst₁
    prf3′ = refl

    prf3′′ : proj₂ (proj₂ (product A B)) {A ⊗ B} ≡ snd
    prf3′′ = refl

    prf3 : proj₁
              (proj₂ (proj₂ (product A B)) (proj₁ (product A B))
                (proj₁ (proj₂ (product A B))))
              ≡
            proj₁ (snd fst fst₁)
    prf3 = refl

    prf4 : proj₁ (snd fst fst₁) ≡ id
    prf4 = sym (w id (sym right-id , sym right-id))

    -- prf4′ = trans prf3 prf4

    prf3′ : proj₁
              (proj₂ (proj₂ (product A B)) (proj₁ (product A B))
                (proj₁ (proj₂ (product A B))))
              ≡
            proj₁ (snd fst fst₁)
    prf3′ = refl

-- y : product-proj₁ (product A B) ≡
--           fst ∘
--           proj₁
--           (snd (product-proj₁ (product A B)) (product-proj₂ (product A B)))

    q : proj₁
        (proj₂ (proj₂ (product A B)) (proj₁ (product A B))
          (proj₁ (proj₂ (product A B))))
        ≡
        proj₁
        (proj₂ (proj₂ (product A B)) (product-proj₁ (product A B))
          (product-proj₂ (product A B)))
    q = w fst₂ (trans prf (sym (rewrite-right-∘ p right-id)) , trans (sym right-id) (rewrite-right-∘ (trans prf3 prf4) refl))


    s : bimap _⊗_ product id id
              ≡
          proj₁
          (proj₂ (proj₂ (product A B))
            (id ∘ proj₁ (product A B))
            (id ∘ proj₁ (proj₂ (product A B))))
    s = refl

    s′ : proj₁
          (proj₂ (proj₂ (product A B))
            (id ∘ proj₁ (product A B))
            (id ∘ proj₁ (proj₂ (product A B))))
          ≡
          proj₁
          (proj₂ (proj₂ (product A B))
            (proj₁ (product A B))
            (proj₁ (proj₂ (product A B))))
    s′ =
      cong₂ (λ x₁ x₂ → proj₁ (proj₂ (proj₂ (product A B)) x₁ x₂))
        left-id
        left-id
  in
  trans (trans s s′) (trans q (trans prf3′ prf4))

bimap-canon : ∀ {X Y Z W} {u : X ⇒ Y} {v : Z ⇒ W} →
  (_⊗_ : Obj → Obj → Obj) →
  (product : ∀ X Y → IsProduct X Y (X ⊗ Y)) →
  (bimap _⊗_ product u v)
      ≡
  proj₁
    (proj₂ (proj₂ (product Y W))
      (u ∘ proj₁ (product X Z))
      (v ∘ proj₁ (proj₂ (product X Z))))
bimap-canon _ _ = refl

bimap-proj₁ : ∀ {X Y Z W} {u : X ⇒ Y} {v : Z ⇒ W} →
  (_⊗_ : Obj → Obj → Obj) →
  (product : ∀ X Y → IsProduct X Y (X ⊗ Y)) →
  (product-proj₁ (product Y W) ∘ bimap _⊗_ product u v)
    ≡
  (u ∘ product-proj₁ (product X Z))
bimap-proj₁ {X} {Y} {Z} {W} {u} {v} _⊗_ product =
  let
    _ , _ , univ = product Y W
    _ , (prf1 , _) , _ = univ (u ∘ product-proj₁ (product X Z)) (v ∘ product-proj₂ (product X Z))
  in
  sym prf1

bimap-proj₂ : ∀ {X Y Z W} {u : X ⇒ Y} {v : Z ⇒ W} →
  (_⊗_ : Obj → Obj → Obj) →
  (product : ∀ X Y → IsProduct X Y (X ⊗ Y)) →
  (product-proj₂ (product Y W) ∘ bimap _⊗_ product u v)
    ≡
  (v ∘ product-proj₂ (product X Z))
bimap-proj₂ {X} {Y} {Z} {W} {u} {v} _⊗_ product =
  let
    _ , _ , univ = product Y W
    _ , (_ , prf2) , _ = univ (u ∘ product-proj₁ (product X Z)) (v ∘ product-proj₂ (product X Z))
  in
  sym prf2

-- product-proj₁-id : ∀ {A B S T} {f : A ⇒ S} {g : B ⇒ T} →
--   (_⊗_ : Obj → Obj → Obj) →
--   (product : ∀ X Y → IsProduct X Y (X ⊗ Y)) →
--   product-proj₁ (product S T) ∘ proj₁
--                                   (proj₂ (proj₂ (product S T)) (f ∘ proj₁ (product A B))
--                                   (g ∘ proj₁ (proj₂ (product A B))))
--     ≡
--   f ∘ product-proj₁ (product A B)
-- product-proj₁-id {A} {B} {S} {T} {f} {g} _⊗_ product = bimap-proj₁ _⊗_ product

bimap-canon-folded : ∀ {X Y Z W} {u : X ⇒ Y} {v : Z ⇒ W} →
  (_⊗_ : Obj → Obj → Obj) →
  (product : ∀ X Y → IsProduct X Y (X ⊗ Y)) →
  (bimap _⊗_ product u v)
      ≡
  proj₁
    (proj₂ (proj₂ (product Y W))
      (product-proj₁ (product Y W) ∘ (bimap _⊗_ product u v))
      (product-proj₂ (product Y W) ∘ (bimap _⊗_ product u v)))
bimap-canon-folded {X} {Y} {Z} {W} {u} {v} _⊗_ product =
  let
    uv = bimap _⊗_ product u v

    a , b , c = product Y W

    f , m1 , m2 = c (product-proj₁ (product Y W) ∘ uv) (product-proj₂ (product Y W) ∘ uv)

    n = m2 (bimap _⊗_ product u v) (refl , refl)
  in
  n

bimap-∘ : ∀ {X Y Z W Y′ W′} {u : X ⇒ Y} {v : Z ⇒ W} {u′ : Y ⇒ Y′} {v′ : W ⇒ W′} →
  (_⊗_ : Obj → Obj → Obj) →
  (product : ∀ X Y → IsProduct X Y (X ⊗ Y)) →
  (bimap _⊗_ product u′ v′ ∘ bimap _⊗_ product u v)
    ≡
  bimap _⊗_ product (u′ ∘ u) (v′ ∘ v)
bimap-∘ {X} {Y} {Z} {W} {Y′} {W′} {u} {v} {u′} {v′} _⊗_ product =
  let
    q , r , m = product Y′ W′

    b = bimap _⊗_ product (u′ ∘ u) (v′ ∘ v)

    m' , prf1 , univ = m (product-proj₁ (product Y′ W′) ∘ b) (product-proj₂ (product Y′ W′) ∘ b)

    h = proj₁
          (proj₂ (proj₂ (product Y′ W′)) ((u′ ∘ u) ∘ proj₁ (product X Z))
            ((v′ ∘ v) ∘ proj₁ (proj₂ (product X Z))))

    univ-h :
        proj₁
        (proj₂ (proj₂ (product Y′ W′))
          ((u′ ∘ u) ∘ proj₁ (product X Z))
          ((v′ ∘ v) ∘ proj₁ (proj₂ (product X Z))))
        ≡
        proj₁
        (proj₂ (proj₂ (product Y′ W′))
          (product-proj₁ (product Y′ W′) ∘
          bimap _⊗_ product (u′ ∘ u) (v′ ∘ v))
          (product-proj₂ (product Y′ W′) ∘
          bimap _⊗_ product (u′ ∘ u) (v′ ∘ v)))

    univ-h = univ h (refl , refl)

    q : (f : (X ⊗ Z) ⇒ Y′) (g : (X ⊗ Z) ⇒ W′) →
        Σ![ (X ⊗ Z) ⇒ Y′ ⊗ W′ ]
        (λ m₁ →
            f ≡ proj₁ (product Y′ W′) ∘ m₁ ×
            g ≡ proj₁ (proj₂ (product Y′ W′)) ∘ m₁)

    q = proj₂ (proj₂ (product Y′ W′))

    canon0 = sym (bimap-canon {W′ ⊗ W′} {W′ ⊗ W′} {W′ ⊗ W′} {W′ ⊗ W′} {Category.id ℂ} {Category.id ℂ} _⊗_ product)

    canon :
        proj₁
        (q
          (product-proj₁ (product Y′ W′) ∘
          bimap _⊗_ product (u′ ∘ u) (v′ ∘ v))
          (product-proj₂ (product Y′ W′) ∘
          bimap _⊗_ product (u′ ∘ u) (v′ ∘ v)))
          ≡
        bimap _⊗_ product (u′ ∘ u) (v′ ∘ v)
    canon = sym (bimap-canon-folded _⊗_ product)

    univ-h′ :  proj₁
        (proj₂ (proj₂ (product Y′ W′)) ((u′ ∘ u) ∘ proj₁ (product X Z))
          ((v′ ∘ v) ∘ proj₁ (proj₂ (product X Z))))
        ≡ bimap _⊗_ product (u′ ∘ u) (v′ ∘ v)
    univ-h′ = refl

    h2 = bimap _⊗_ product u′ v′ ∘ bimap _⊗_ product u v

    univ-h2-0 : (u′ ∘ u) ∘ product-proj₁ (product X Z) ≡
                  proj₁ (product Y′ W′) ∘
                  proj₁
                  (proj₂ (proj₂ (product Y′ W′)) (u′ ∘ proj₁ (product Y W))
                  (v′ ∘ proj₁ (proj₂ (product Y W))))
                  ∘ bimap _⊗_ product u v
    univ-h2-0 =
      trans (trans ∘-assoc (rewrite-right-∘ (bimap-proj₁ _⊗_ product) refl)) (trans (sym ∘-assoc) (rewrite-left-∘ (bimap-proj₁ _⊗_ product) ∘-assoc))

    univ-h2-1 : (v′ ∘ v) ∘ product-proj₂ (product X Z) ≡
                  proj₁ (proj₂ (product Y′ W′)) ∘
                  proj₁
                  (proj₂ (proj₂ (product Y′ W′)) (u′ ∘ proj₁ (product Y W))
                  (v′ ∘ proj₁ (proj₂ (product Y W))))
                  ∘ bimap _⊗_ product u v
    univ-h2-1 =
      trans (trans ∘-assoc (rewrite-right-∘ (bimap-proj₂ _⊗_ product) refl)) (trans (sym ∘-assoc) (rewrite-left-∘ (bimap-proj₂ _⊗_ product) ∘-assoc))

    univ-h2 = univ h2
      (trans (bimap-proj₁ _⊗_ product) (trans univ-h2-0 (trans (rewrite-right-∘ (rewrite-left-∘ (sym (bimap-canon _⊗_ product)) refl) refl) (rewrite-right-∘ (rewrite-left-∘ (sym (bimap-canon _⊗_ product)) refl) refl)))
        ,
        trans (bimap-proj₂ _⊗_ product) (trans univ-h2-1 (trans (rewrite-right-∘ (rewrite-left-∘ (sym (bimap-canon _⊗_ product)) refl) refl) (rewrite-right-∘ (rewrite-left-∘ (sym (bimap-canon _⊗_ product)) refl) refl)))
      )

    w = trans (bimap-canon-folded _⊗_ product) (sym univ-h2)
  in
    sym w



IsExponential : ∀ {A B : Obj} →
  (_⊗_ : Obj → Obj → Obj) →
  (∀ X Y → IsProduct X Y (X ⊗ Y)) →
  (A⟶B : Obj) →
  (ev : (A⟶B ⊗ A) ⇒ B) →
  Set (o ⊔ ℓ)
IsExponential {A} {B} _⊗_ product A⟶B ev =
  ∀ Z (e : (Z ⊗ A) ⇒ B) →
    Σ![ Z ⇒ A⟶B ] λ u →
      (ev ∘ bimap _⊗_ product u (id {A}))
        ≡
      e

-- Natural numbers object
IsNNO : ∀ {𝟙 ℕ} →
  (𝟙-terminal : IsTerminal 𝟙)
  (z : 𝟙 ⇒ ℕ) →
  (s : ℕ ⇒ ℕ) →
  Set (o ⊔ ℓ)
IsNNO {𝟙} {ℕ} 𝟙-terminal z s =
  ∀ {A} →
    (q : 𝟙 ⇒ A) →
    (f : A ⇒ A) →
    Σ![ ℕ ⇒ A ] λ u →
      ((u ∘ (s ∘ z)) ≡ (f ∘ q))
        ×
      ((u ∘ z) ≡ q)
