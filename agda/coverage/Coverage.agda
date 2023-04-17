{-# OPTIONS --without-K #-}

module Coverage where

open import Data.Unit.Base
open import Data.Empty

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base as List using (List; []; _∷_; _++_; null)
import Data.List.Effectful as List
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListR using (here; there; _─_)
open import Data.List.Relation.Unary.Any.Properties using (++⁻; ─⁻; ─⁺)

open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_; _⁺++⁺_; toList)
import Data.List.NonEmpty.Effectful as List⁺
open import Data.List.NonEmpty.Relation.Unary.Any as List⁺R using (here; there)
open import Data.List.NonEmpty.Relation.Unary.Any.Properties as List⁺R
  using (⁺++⁺⁻; ⁺++⁺⁺ˡ; ⁺++⁺⁺ʳ; toList⁻)

open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)

open import Data.Product as Prod using (Σ; ∃; _×_; _,_; -,_; Σ-syntax; proj₁; proj₂)
import Data.Product.Relation.Unary.All as Prod

open import Data.SnocList.Base using (SnocList; []; _:<_; _<>>_; _<><_)
open import Data.SnocList.Relation.Unary.Any as Any using (<>>⁺ʳ; <>>⁺ˡ)
open import Data.SnocList.Relation.Unary.All using (<>>⁺; <>>⁻; <><⁺)

open import Data.String using (String; _≟_)

open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)

open import Effect.Applicative using (module RawApplicative; module RawAlternative)

open import Function.Base using (id; const; _∘_; _∘′_; case_of_; _$_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

data Singleton {a} {A : Set a} : (x : A) → Set a where
  [_] : (x : A) → Singleton x

data Desc : Set where
  `AtomBar : List String → Desc
  `Prod : Desc → Desc → Desc
  `EnumOrTag : List String → List (String × Desc) → Desc
  `X : Desc

pattern `Atom = `AtomBar []

{-# TERMINATING #-}
⟦_⟧ : Desc → Set → Set
⟦ `X                ⟧ X = X
⟦ `AtomBar ats      ⟧ X = Σ[ at ∈ String ] All (at ≢_) ats
⟦ `Prod d₁ d₂       ⟧ X = ⟦ d₁ ⟧ X × ⟦ d₂ ⟧ X
⟦ `EnumOrTag es tds ⟧ X
  = ListR.Any Singleton es
  ⊎ ListR.Any (Prod.All Singleton λ d → ⟦ d ⟧ X) tds

data `μ (d : Desc) : Set where
  `in : ⟦ d ⟧ (`μ d) → `μ d

Tree : Desc
Tree = `EnumOrTag ("leaf" ∷ []) (("node" , `Prod `X (`Prod `Atom `X)) ∷ [])

leaf : `μ Tree
leaf = `in (inj₁ (here [ "leaf" ]))

node : `μ Tree → String → `μ Tree → `μ Tree
node l v r = `in (inj₂ (here ([ "node" ] , l , (v , []) , r)))

example : `μ Tree
example = node (node leaf "hello" leaf) " " (node (node leaf "world" leaf) "!" leaf)

data Pat : Set where
  `var  : Pat
  `atom : String → Pat
  `cons : Pat → Pat → Pat

data ⟦_⟧μ_∋_ : (d ini : Desc) → Pat → Set where
  `var  : ∀ {d ini} → ⟦ d ⟧μ ini ∋ `var
  `atom : ∀ {ats ini} → (at : String) → All (at ≢_) ats → ⟦ `AtomBar ats ⟧μ ini ∋ `atom at
  `cons : ∀ {p q d e ini} → ⟦ d ⟧μ ini ∋ p → ⟦ e ⟧μ ini ∋ q → ⟦ `Prod d e ⟧μ ini ∋ (`cons p q)
  `enum : ∀ {es tds ini} (at : String) → ListR.Any (at ≡_) es → ⟦ `EnumOrTag es tds ⟧μ ini ∋ `atom at
  `tag  : ∀ {es tds ini} (t : String) {d p} → ListR.Any ((t , d) ≡_) tds →
          ⟦ d ⟧μ ini ∋ p → ⟦ `EnumOrTag es tds ⟧μ ini ∋ `cons (`atom t) p
  `in   : ∀ {ini p} → ⟦ ini ⟧μ ini ∋ p → ⟦ `X ⟧μ ini ∋ p

module _ (ini d : Desc) where

  Sound : (partition : List⁺ Desc × List Desc) → Set
  Sound (t , l)
    = (p : Pat)
    → ((∃ λ d → List⁺R.Any (d ≡_) t × ⟦ d ⟧μ ini ∋ p)
       ⊎ ∃ λ d → ListR.Any (d ≡_) l × ⟦ d ⟧μ ini ∋ p)
    → ⟦ d ⟧μ ini ∋ p

  Complete : (partition : List⁺ Desc × List Desc) → Set
  Complete (t , l)
    = (p : Pat) → ⟦ d ⟧μ ini ∋ p
    → (∃ λ d → List⁺R.Any (d ≡_) t × ⟦ d ⟧μ ini ∋ p)
    ⊎ All (λ d → Maybe (⟦ d ⟧μ ini ∋ p)) l

  record Split : Set where
    constructor mkSplit
    field
      partition : List⁺ Desc × List Desc
      sound     : Sound partition
      complete  : Complete partition
  open Split public

check : ∀ {a} {A : Set a} {x y : A} {xs} (p : ListR.Any (x ≡_) xs) (q : ListR.Any (y ≡_) xs) →
        Σ (x ≡ y) (λ where P.refl → p ≡ q) ⊎ ListR.Any (y ≡_) (xs ─ p)
check (here P.refl) (here P.refl) = inj₁ (P.refl , P.refl)
check (here px) (there q) = inj₂ q
check (there p) (here eq) = inj₂ (here eq)
check (there p) (there q)
  = Sum.map
    (λ where (P.refl , eq) → P.refl , P.cong there eq)
    there
    (check p q)

_\\_  : ∀ {ini} (d : Desc) {p} → ⟦ d ⟧μ ini ∋ p → Split ini d
d \\ `var = record
  { partition = d ∷ [] , []
  ; sound = λ p → [ (λ where (d , here P.refl , prf) → prf)
                  , (λ where (d , () , prf)) ]′
  ; complete = λ p prf → inj₁ (d , here P.refl , prf) }
`AtomBar ats \\ `atom at at∉ats = record
  { partition = (`EnumOrTag (at ∷ []) []) ∷ [] , `AtomBar (at ∷ ats) ∷ []
  ; sound = λ p →
          [ (λ where
                (_ , here P.refl , `enum at (here P.refl)) → `atom at at∉ats
                (_ , here P.refl , `tag p () q)
                (_ , here P.refl , `var) → `var)
          , (λ where
                (_ , here P.refl , `var) → `var
                (_ , here P.refl , `atom at′ (_ ∷ at′∉ats)) → `atom at′ at′∉ats)
          ]′
  ; complete = λ where
     _ `var → inj₂ (just `var ∷ [])
     _ (`atom at′ at′∉ats) → case at′ ≟ at of λ where
      (yes eq) → inj₁ (`EnumOrTag (at ∷ []) [] , here P.refl , `enum at′ (here eq))
      (no ¬eq) → inj₂ ((just (`atom at′ (¬eq ∷ at′∉ats))) ∷ []) }
`Prod d₁ d₂ \\ `cons p₁ p₂
  = let mkSplit (t₁ , l₁) snd₁ cmp₁ = d₁ \\ p₁
        mkSplit (t₂ , l₂) snd₂ cmp₂ = d₂ \\ p₂
        ts = let open RawApplicative List⁺.applicative in ⦇ `Prod t₁ t₂ ⦈
        ls = let open RawApplicative List.applicative in
             ⦇ `Prod (toList t₁) l₂ ⦈ ++ ⦇ `Prod l₁ (toList t₂) ⦈ ++ ⦇ `Prod l₁ l₂ ⦈
  in record
  { partition
    = ts , ls
  ; sound = λ p →
      [ {!!}
      , {!!}
      ]′
  ; complete = λ where
    _ `var → if null ls
             then inj₁ (_ , here P.refl , `var)
             else inj₂ (All.tabulate (const $ just `var))
    _ (`cons prf₁ prf₂) → case (cmp₁ _ prf₁ , cmp₂ _ prf₂) of λ where
      (inj₁ (d₁ , any₁ , prf₁) , inj₁ (d₂ , any₂ , prf₂)) → inj₁ (`Prod d₁ d₂ , {!!} , `cons prf₁ prf₂)
      (inj₁ (d₁ , any₁ , prf₁) , inj₂ r₂) → inj₂ {!!}
      (inj₂ r₁ , inj₁ (d₂ , any₂ , prf₂)) → inj₂ {!!}
      (inj₂ r₁ , inj₂ r₂) → inj₂ {!!} }
`EnumOrTag (at ∷ []) [] \\ `enum at (here P.refl) = record
  { partition = `EnumOrTag (at ∷ []) [] ∷ [] , []
  ; sound = λ where p (inj₁ (d , here P.refl , prf)) → prf
  ; complete = λ where p prf → inj₁ (`EnumOrTag (at ∷ []) [] , here P.refl , prf) }

`EnumOrTag es tds \\ `enum at at∈es = let es = es ─ at∈es in record
  { partition = `EnumOrTag (at ∷ []) [] ∷ []
              , `EnumOrTag es tds ∷ []
  ; sound = λ p →
    [ (λ where
         (_ , here P.refl , `var) → `var
         (_ , here P.refl , `enum at (here P.refl)) → `enum at at∈es)
    , (λ where
         (_ , here P.refl , `var) → `var
         (_ , here P.refl , `enum at at∈del) → `enum at (─⁻ at∈es at∈del)
         (_ , here P.refl , `tag t t∈tds prf) → `tag t t∈tds prf)
    ]′
  ; complete = λ where
      _ `var → inj₂ (just `var ∷ [])
      _ (`enum at′ at′∈es) → case at′ ≟ at of λ where
        (yes eq) → inj₁ (`EnumOrTag (at ∷ []) [] , here P.refl , `enum at′ (here eq))
        (no ¬eq) → inj₂ ((just (`enum at′ (─⁺ at∈es (λ _ (eq₁ , eq₂) → ¬eq (P.trans eq₁ (P.sym eq₂))) at′∈es))) ∷ [])
      _ (`tag t any prf) → inj₂ (just (`tag t any prf) ∷ []) }
`EnumOrTag es tds \\ `tag tag {d = d} td∈tds p with (d \\ p)
`EnumOrTag [] ((tag , d) ∷ []) \\ `tag tag {d = d} (here P.refl) p | mkSplit (t , []) snd cmp
  = record
  { partition = `EnumOrTag [] ((tag , d) ∷ []) ∷ [] , []
  ; sound = λ where p (inj₁ (_ , here P.refl , prf)) → prf
  ; complete = λ p prf → inj₁ (_ , here P.refl , prf) }
`EnumOrTag es tds \\ `tag tag {d = d} td∈tds p  | mkSplit (t , []) snd cmp
  = let tds = tds ─ td∈tds in record
  { partition = `EnumOrTag [] ((tag , d) ∷ []) ∷ [] , `EnumOrTag es tds ∷ []
  ; sound = λ p →
    [ (λ where
     (_ , here P.refl , `var) → `var
     (_ , here P.refl , `tag tag (here P.refl) prf) → `tag tag td∈tds prf)
    , (λ where
        (_ , here P.refl , `var) → `var
        (_ , here P.refl , `enum at at∈es) → `enum at at∈es
        (_ , here P.refl , `tag tag td′∈tds prf) → `tag tag (─⁻ td∈tds td′∈tds) prf)
    ]′
  ; complete = λ where
      _ `var → inj₂ (just `var ∷ [])
      _ (`enum at at∈es) → inj₂ (just (`enum at at∈es) ∷ [])
      _ (`tag tag′ td′∈tds prf) → case check td∈tds td′∈tds of λ where
        (inj₁ eq) → inj₁ (_ , here P.refl , `tag tag′ (here (P.sym (proj₁ eq))) prf)
        (inj₂ td∈tds─) → inj₂ (just (`tag tag′ td∈tds─ prf) ∷ []) }
... | mkSplit (t , l) snd cmp = record
  { partition = `EnumOrTag [] (toList (List⁺.map (tag ,_) t)) ∷ []
                 -- note: it's not true anymore that all tags are unique
              , `EnumOrTag es (List.map (tag ,_) l ++ (tds ─ td∈tds)) ∷ []
  ; sound = λ p →
    [ (λ where
        (_ , here P.refl , `var) → `var
        (_ , here P.refl , `tag tag′ td′∈tds prf) →
          let any′ = toList⁻ td′∈tds
              any = List⁺R.map⁻ (List⁺R.map (P.cong proj₂) any′)
              eq  = P.cong proj₁ $ proj₂ $ List⁺R.satisfied (List⁺R.map⁻ any′)
          in `tag tag′ (case eq of λ where P.refl → td∈tds) (snd _ (inj₁ (_ , any , prf))))
    , {!!}
    ]′
  ; complete = {!!} }
`X \\ `in p = let mkSplit spl@(t , l) snd cmp = _ \\ p in record
  { partition = spl
  ; sound = λ p → `in ∘′ snd p
  ; complete = λ where
      _ `var → cmp `var `var
      _ (`in prf) → cmp _ prf }

embed : ∀ {ini d} →
        (spl : Split ini d) →
        All (Maybe ∘′ Split ini) (proj₂ (partition spl)) →
        Split ini d
embed {ini} {d} spl alls = go [] alls (sound spl) (complete spl) where

  go : ∀ {cs} lsˡ {lsʳ} →
       All (Maybe ∘′ Split ini) lsʳ →
       Sound ini d (cs , lsˡ <>> lsʳ) →
       Complete ini d (cs , lsˡ <>> lsʳ) →
       Split ini d
  go lsˡ [] snd cmp = record
    { sound = snd
    ; complete = cmp }
  go lsˡ {lsʳ = l₁ ∷ _} (nothing ∷ alls) snd cmp = go (lsˡ :< l₁) alls snd cmp
  go {cs} lsˡ {lsʳ = lʳ ∷ lsʳ} (just (mkSplit (c₁ , l₁) snd₁ cmp₁) ∷ alls) snd cmp
    = go {cs = c₁ ⁺++⁺ cs} (lsˡ <>< l₁) alls
       (λ p → [ (λ (d , any , prf) →
                   [ (λ any → let prf = snd₁ p (inj₁ (d , any , prf)) in
                              snd p (inj₂ (_ , <>>⁺ʳ lsˡ (here P.refl) , prf)))
                   , (λ any → snd p (inj₁ (d , any , prf)))
                   ]′ (⁺++⁺⁻ c₁ any))
              , (λ (d , any , prf) →
                   [ (λ any → snd p (inj₂ (d , <>>⁺ʳ lsˡ (there any) , prf)))
                   , (λ any →
                        [ (λ any → snd p (inj₂ (d , <>>⁺ˡ any , prf)))
                        , (λ any → let prf = snd₁ p (inj₂ (d , any , prf)) in
                          snd p (inj₂ (lʳ , <>>⁺ʳ lsˡ (here P.refl) , prf)))
                        ]′ (Any.<><⁻ l₁ any))
                   ]′ (Any.<>>⁻ (lsˡ <>< l₁) any))
              ]′)
       (λ p prf →
         [ (λ (d , all , prf) → inj₁ (d , ⁺++⁺⁺ʳ c₁ all , prf))
         , (λ all → case <>>⁻ lsˡ all of λ where
             (plsˡ , nothing ∷ plsʳ) → inj₂ (<>>⁺ (<><⁺ plsˡ (All.tabulate {xs = l₁} (const nothing))) plsʳ)
             (plsˡ , just prf ∷ plsʳ) →
               [ (λ (d , any , prf) → inj₁ (d , ⁺++⁺⁺ˡ any , prf))
               , (λ all → inj₂ (<>>⁺ (<><⁺ plsˡ all) plsʳ))
               ]′ (cmp₁ p prf))
         ]′ (cmp p prf))



coverage : ∀ {ini d} → List⁺ (Σ[ p ∈ Pat ] ⟦ d ⟧μ ini ∋ p) → Pat ⊎ Split ini d
coverage {ini} {d} ((p , prf) ∷ ps) = go (_ \\ prf) ps where

  go : Split ini d → List (Σ[ p ∈ Pat ] ⟦ d ⟧μ ini ∋ p) → Pat ⊎ Split ini d
  go spl [] = inj₂ spl
  go spl ((p , prf) ∷ ps) = case complete spl p prf of λ where
    (inj₁ covered) → inj₁ p
    (inj₂ matches) → go (embed spl (All.map (Maybe.map (_ \\_)) matches)) ps

-- In
-- case t of
--   { 'leaf → ...
--   ; ['node [x y]] → ...
--   ; ['node bs] → ...
--   }
-- the ['node bs] branch is already covered by the ['node [x y]] one
_ : coverage {ini = Tree} {d = Tree}
      ( (-, `enum "leaf" (here P.refl))
      ∷ (-, `tag "node" (here P.refl) (`cons `var `var))
      ∷ (-, `tag "node" (here P.refl) `var)
      ∷ [])
  ≡ inj₁ (`cons (`atom "node") `var)
_ = P.refl

_ : coverage {ini = Tree} {d = `Atom}
     ( (-, `atom "oops" [])
     ∷ (-, `atom "ok" [])
     ∷ (-, `atom "fine" [])
     ∷ (-, `atom "alright" [])
     ∷ (-, `atom "oops" [])
     ∷ [])
  ≡ inj₁ (`atom "oops")
_ = P.refl
