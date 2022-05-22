{-# OPTIONS --safe --without-K #-}

-- This is a solution to the problem posed in:
-- http://math.andrej.com/2022/05/20/one-syntax-to-rule-them-all/


{-
   An attempt at formalization of (raw) higher-rank syntax.

   We define a notion of syntax which allows for higher-rank binders,
   variables and substitutions. Ordinary notions of variables are
   special cases:

   * order 1: ordinary variables and substitutions, for example those of
     λ-calculus
   * order 2: meta-variables and their instantiations
   * order 3: symbols (term formers) in dependent type theory, such as
     Π, Σ, W, and syntactic transformations between theories

   The syntax is parameterized by a type Class of syntactic classes. For
   example, in dependent type theory there might be two syntactic
   classes, ty and tm, corresponding to type and term expressions.
-}

module Syntax (Class : Set) where

  {- Shapes can also be called “syntactic variable contexts”, as they assign to
     each variable its syntactic arity, but no typing information.

     An arity is a binding shape with a syntactic class. The shape specifies
     how many arguments the variable takes and how it binds the argument's variables.
     The class specifies the syntactic class of the variable, and therefore of the
     expression formed by it.

     We model shapes as binary trees so that it is easy to concatenate
     two of them. A more traditional approach models shapes as lists, in
     which case one has to append lists.
  -}

  infixl 6 _⊕_

  data Shape : Set where
    𝟘 : Shape -- the empty shape
    [_,_] : ∀ (γ : Shape) (cl : Class) → Shape -- the shape with precisely one variable
    _⊕_ : ∀ (γ : Shape) (δ : Shape) → Shape -- disjoint sum of shapes

  infix 5 [_,_]∈_

  {- The de Bruijn indices are binary numbers because shapes are binary
     trees. [ δ , cl ]∈ γ is the set of variable indices in γ whose arity
     is (δ, cl). -}

  data [_,_]∈_ : Shape → Class → Shape → Set where
    var-here : ∀ {θ} {cl} → [ θ , cl ]∈  [ θ , cl ]
    var-left :  ∀ {θ} {cl} {γ} {δ} → [ θ , cl ]∈ γ → [ θ , cl ]∈ γ ⊕ δ
    var-right : ∀ {θ} {cl} {γ} {δ} → [ θ , cl ]∈ δ → [ θ , cl ]∈ γ ⊕ δ


  data All (p : Shape → Class → Set) : Shape → Set where
    𝟘 : All p 𝟘
    [_] : ∀ {γ cl} → p γ cl → All p [ γ , cl ]
    _⊕_ : ∀ {γ δ} → All p γ → All p δ → All p (γ ⊕ δ)

  tabulate : ∀ {δ p} → (∀ {γ cl} → [ γ , cl ]∈ δ → p γ cl) → All p δ
  tabulate {𝟘} f = 𝟘
  tabulate {[ δ , cl ]} f = [ f var-here ]
  tabulate {δ ⊕ δ₁} f = tabulate (λ z → f (var-left z)) ⊕ tabulate (λ z → f (var-right z))

  lookup : ∀ {δ p} → All p δ → (∀ {γ cl} → [ γ , cl ]∈ δ → p γ cl)
  lookup [ pv ] var-here = pv
  lookup (ρ ⊕ _) (var-left v) = lookup ρ v
  lookup (_ ⊕ ρ) (var-right v) = lookup ρ v


  map : ∀ {δ p q} → (∀ {γ cl} → p γ cl → q γ cl) → All p δ → All q δ
  map f ps = tabulate (λ v → f (lookup ps v))

  {- Examples:

  postulate ty : Class -- type class
  postulate tm : Class -- term class

  ordinary-variable-arity : Class → Shape
  ordinary-variable-arity c = [ 𝟘 , c ]

  binary-type-metavariable-arity : Shape
  binary-type-metavariable-arity = [ [ 𝟘 , tm ] ⊕ [ 𝟘 , tm ] , ty ]

  Π-arity : Shape
  Π-arity = [ [ 𝟘 , ty ] ⊕ [ [ 𝟘 , tm ] , ty ] , ty ]

  -}

  {- Because everything is a variable, even symbols, there is a single
     expression constructor _`_ which forms and expression by applying
     the variable x to arguments ts. -}

  -- Expressions

  infix 9 _`_

  data Expr : Shape → Class → Set where
    _`_ : ∀ {γ} {δ} {cl} (x : [ δ , cl ]∈ γ) →
            (ts : All (λ θ B → Expr (γ ⊕ θ) B) δ) → Expr γ cl

  -- Renamings

  infix 5 _→ʳ_

  _→ʳ_ : Shape → Shape → Set
  γ →ʳ δ = All ([_,_]∈ δ) γ

  -- identity renaming

  𝟙ʳ : ∀ {γ} → γ →ʳ γ
  𝟙ʳ = tabulate (λ z → z)

  -- composition of renamings

  infixl 7 _∘ʳ_

  _∘ʳ_ : ∀ {γ} {δ} {η} → (δ →ʳ η) → (γ →ʳ δ) → (γ →ʳ η)
  (r ∘ʳ s) = tabulate (λ v → lookup r (lookup s v))

  -- renaming extension

  ⇑ʳ : ∀ {γ δ Θ} → (γ →ʳ δ) → (γ ⊕ Θ →ʳ δ ⊕ Θ)
  ⇑ʳ r = map var-left r ⊕ map var-right 𝟙ʳ

  ⇑ˡ : ∀ {γ δ Θ} → (γ →ʳ δ) → (Θ ⊕ γ →ʳ Θ ⊕ δ)
  ⇑ˡ r = map var-left 𝟙ʳ ⊕ map var-right r

  -- the action of a renaming on an expression

  infixr 6 [_]ʳ_

  [_]ʳ_ : ∀ {γ δ cl} (r : γ →ʳ δ) → Expr γ cl → Expr δ cl
  [_]ʳˢ_ : ∀ {γ δ η} (r : γ →ʳ δ) → All (λ θ → Expr (γ ⊕ θ)) η → All (λ θ → Expr (δ ⊕ θ)) η

  [ r ]ʳ (x ` ts) = lookup r x ` [ r ]ʳˢ ts

  [ r ]ʳˢ 𝟘 = 𝟘
  [ r ]ʳˢ [ t ] = [ [ map var-left r ⊕ map var-right 𝟙ʳ ]ʳ t ]
  [ r ]ʳˢ (tsˡ ⊕ tsʳ) = ([ r ]ʳˢ tsˡ) ⊕ ([ r ]ʳˢ tsʳ)

  -- substitution
  infix 5 _→ˢ_

  _→ˢ_ : Shape → Shape → Set
  γ →ˢ δ = All (λ θ → Expr (δ ⊕ θ)) γ

  lift : ∀ {γ δ} → (γ →ʳ δ) → (γ →ˢ δ)
  lift 𝟘 = 𝟘
  lift [ ρ ] = [ var-left ρ ` lift (map var-right 𝟙ʳ) ]
  lift (ρˡ ⊕ ρʳ) = lift ρˡ ⊕ lift ρʳ

  -- side-remark: notice that the ts in the definition of Expr is just a substituition

  -- We now hit a problem when trying to define the identity substitution in a naive
  -- fashion. Agda rejects the definition, as it is not structurally recursive.
  𝟙ˢ : ∀ {γ} → γ →ˢ γ
  𝟙ˢ = lift 𝟙ʳ

{-
  {- What is the best way to deal with the non-termination problem? I have tried:

     1. sized types: got mixed results, perhaps I don't know how to use them
     2. well-founded recursion: it gets messy and unpleasant to use
     3. reorganizing the above definitions, but non-structural recursion always sneeks in

     A solution which makes the identity substitition compute is highly preferred.

     The problem persists with other operations on substitutions, such as composition
     and the action of a substitution.
  -}
-}
