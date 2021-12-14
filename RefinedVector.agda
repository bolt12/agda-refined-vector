module RefinedVector where

open import Level using (Level) renaming (zero to 0ℓ; suc to suc-ℓ)
open import Data.Nat
open import Relation.Binary
open import Relation.Nullary using (_because_; yes; no)
open import Data.Bool using (true; false)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (map to map-×)
open import Data.Sum

module Unit where

  record ⊤ {ℓ : Level} : Set ℓ where
    instance constructor tt

module Attempt1 where
  -- I have been sitting on this idea for a while: What could I possible do with a refined vector
  -- data structure that could give me some guarantees about the order of its elements?
  --
  -- I had two questions in mind:
  --   - Would I be able to prove that a vector indexed by the bottom
  --     relation (i.e. no two elements are related) has length 0 ?
  --   - Can I write a sorting algorithm the goes from a vector with an arbitrary relation to
  --     one that is ordered?
  --
  -- What more questions could I ask? If it worked then this data type index's would represent
  -- a form of refinement types withing the data structure itself that would allow us to have
  -- correct-by-construction code and also we could aid the compiler to leverage about all information
  -- and have machine-checked proofs about our code.
  
  -- This is the definition I first had in mind. A Vector indexed by natural numbers (the length)
  -- and by an arbitrary homogeneous binary relation (the order of the elements in the vector).
  --
  data Vector {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → Set ℓ where
    -- The empty case constructor is simple, we do not require any proofs using the order
    -- Because there are no elements to compare.
    []      : Vector A _≾_ 0
  
    -- This is the singleton list case. We have it because the cons constructor for this data type
    -- receives 2 elements instead of the standard 1, and I wanted to be able to represent any length
    -- vectors. I am a bit unneasy about my choice here but I had to require some relation with this
    -- singleton element and I picked the reflexive one. Lets hope it doesn't bite me in the future.
    [_]     : ∀ (x : A) {x≾y : x ≾ x} → Vector A _≾_ 1
  
    -- This is where the magic happens. This 2-cons constructor receives 2 elements to cons to a given
    -- vector, but also needs a proof about their order.
    _∷_∷_ : ∀ {n : ℕ} (x : A) (y : A) (xs : Vector A _≾_ n) {x≾y : x ≾ y} → Vector A _≾_ (2 + n) 
  
  -- Great! Now lets see how we could build a strictly ordered natural number vector: 
  test : Vector ℕ (_<_) 2
  test = (1 ∷ 2 ∷ []) {s≤s (s≤s z≤n)}
  
  -- Now lets see if we can answer the first question, which is about proving that for a Vector
  -- indexed by the bottom relation the only possible vector is the empty one.
  absurd-has-length-0 : ∀ {n : ℕ} → Vector ℕ (λ _ _ → ⊥) n → n ≡ 0
  absurd-has-length-0 [] = refl
  
  -- Awesome! Agda managed to prove it just with refl, that's the kind of power I was looking
  -- to provide to the compiler with a data structure formulation like this.
  
  -- Now lets see if we can prove (code) that sorting a ℕ's Vector indexed by an
  -- arbitrary relation, results in an ordered list.
  --
  -- I am thinking about a merge or quicksort, but for that we need to be able to split
  -- the vector in half in each recursive step. For that we need some auxiliary functions:
  
  -- The head function is relatively straightforward:
  head : ∀ {n} {ℓ} {A} {_≾_} → Vector {ℓ} A _≾_ (1 + n) → A
  head [ x ]       = x
  head (x ∷ _ ∷ _) = x
  
  -- It appears that head's counterpart function - tail, is not straightforward due to
  -- the way our data constructors are designed. In order to implement tail I need some
  -- auxiliary function that lets me cons just a single element into a vector.
  --
  -- The challenge here is providing the actual proof that the element I want to cons respects
  -- the order, because we can either be cons-ing the element to an empty list or a non-empty
  -- list. In simpler terms, we either need to provide a reflexive proof or a proof that
  -- the element that we want to add relates with the head of the non-empty vector.
  -- 
  -- Coming with a suitable, ergonomic type signature was hard, but ultimately I found this one
  -- where one passes a function that computes the proof for us, for an arbitrary value.
  cons : ∀ {n} {ℓ} {A} {_≾_ : Rel A ℓ}
       → (a : A)
       → Vector {ℓ} A _≾_ n
       -> ((b : A) → a ≾ b )
       → Vector {ℓ} A _≾_ (1 + n)
  cons a [] f = [ a ] {f a}
  cons a [ x ] f = (a ∷ x ∷ []) {f x}
  cons a (x ∷ y ∷ v) f = (a ∷ y ∷ cons a v f) {f y}
  
  -- This is my miserable attempt to define the tail function on refined vectors. I thought
  -- I needed the cons function but it appears I can not produce the proof I need so easily.
  --
  -- While trying to define tail I discovered a major flaw on my data type which is I can only
  -- enforce the order in a non-transitive way. E.g. the vector 1 2 0 1 would be valid, because
  -- I do not require any proof between 2 and 0.
  --
  -- tail : ∀ {n} {A} {_≾_} {reflexive : Reflexive _≾_}
  --      → Vector A _≾_ (1 + n)
  --      → Vector A _≾_ n
  -- tail [ x ]       = []
  -- tail {reflexive = reflexive} (x ∷ y ∷ v) with v
  -- ... | [] = [ y ] {reflexive {y}}
  -- ... | [ z ] = (y ∷ z ∷ []) {{!!}}
  -- ... | x₁ ∷ y₁ ∷ res = {!!}
  
  -- I need to reformulate my data type.
  
module Attempt2 where

  -- We need to roll our own ⊤ data type, for reasons enumerated below.
  open Unit

  -- After much thinking I think I can maybe fix my problem with a mutual recursive data type.
  -- Here's what I thought about:
  --
  -- Two refined vector types, and in Agda if I want to define mutual recursive data types
  -- I have to provide the type signature first and only then the constructor declarations
  data Vectorᵐ₁ {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → Set ℓ
  data Vectorᵐ₂ {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → Set ℓ

  -- One wrapper to uniformize the API
  Vector : {ℓ : Level} → (A : Set ℓ) → Rel A ℓ → ℕ → Set ℓ
  Vector A _≾_ n = Vectorᵐ₁ A _≾_ n

  -- My two Vector types are going to have only a cons constructor and not a 2-cons constructor.
  -- These head functions take the parameters of the cons constructor and either outputs the head
  -- of the list if it is non-empty or just returns the element to cons.
  --
  -- This is needed to calculate which type of proof one needs to give. If we are consing something
  -- to the empty list we need to provide a reflexive proof, otherwise a relation proof. As we are
  -- going to see below.
  -- NOTE: We have to declare these functions in the same way we are doing for our recursive types
  -- because we are going to have to include them in the data declarations.
  --
  -- Deprecated reason:
  -- Great! Now lets see how we could build a strictly ordered natural number vector.
  -- And woops it appears that requiring a reflexive proof is too restrictive. We should ditch
  -- that.
  --
  -- test : Vector ℕ (_<_) 2
  -- test = (1 ∷ (2 ∷ []) {{!!}}) {s≤s (s≤s z≤n)} 
  -- 
  -- headₐ₁ : ∀ {ℓ} {n} {A} {_≾_} → A → Vectorᵐ₁ {ℓ} A _≾_ n → A
  -- headₐ₁ a [] = a
  -- headₐ₁ _ (x ∷ v) = x
  -- 
  -- headₐ₂ : ∀ {ℓ} {n} {A} {_≾_} → A → Vectorᵐ₂ {ℓ} A _≾_ n → A
  -- headₐ₂ a [] = a
  -- headₐ₂ _ (x ∷ v) = x

  -- My two Vector types are going to have only a cons constructor and not a 2-cons constructor.
  -- These proof-≾ functions take the parameters of the cons constructor and output the required
  -- order proof obligation. If the list is empty we do not require any proof obligation as doing so
  -- would be too restrictive (read above). If the list is non-empty we require a proof obligation
  -- that a ≾ head v.
  proof-≾₁ : ∀ {ℓ} {n} {A} {_≾_} → A → Vectorᵐ₁ {ℓ} A _≾_ n → Set ℓ
  proof-≾₂ : ∀ {ℓ} {n} {A} {_≾_} → A → Vectorᵐ₂ {ℓ} A _≾_ n → Set ℓ

  -- As mentioned above our Vectorᵐ types are mutually recursive. Both have an empty list constructor
  -- and a cons constructor. The cons constructor receives the element to cons, a list of the opposite
  -- type, either Vectorᵐ₁ or Vectorᵐ₂, and a proof that the element we want to cons respects the order
  -- given the result of headₐ, which as I explained above will be either a ≾ a or a ≾ head v .
  data Vectorᵐ₁ {ℓ} A _≾_ where
    []  : Vectorᵐ₁ A _≾_ 0
    _∷_ : ∀ {n} (a : A) (v : Vectorᵐ₂ A _≾_ n) → {a≾b : proof-≾₂ {ℓ} {n} {A} {_≾_} a v} → Vectorᵐ₁ A _≾_ (1 + n)

  data Vectorᵐ₂ {ℓ} A _≾_ where
    []  : Vectorᵐ₂ A _≾_ 0
    _∷_ : ∀ {n} (a : A) (v : Vectorᵐ₁ A _≾_ n) → {a≾b : proof-≾₁ {ℓ} {n} {A} {_≾_} a v} → Vectorᵐ₂ A _≾_ (1 + n)

  -- Finally we define the body of proof-≾ here. Notice the overloading of the constructor operators!
  -- In the empty list case we realise that ⊤ from Data.Unit is not universe polymorphic so we need to
  -- roll our own.
  proof-≾₁ _ [] = ⊤
  proof-≾₁ {_≾_ = _≾_} a (b ∷ v) = a ≾ b

  proof-≾₂ _ [] = ⊤
  proof-≾₂ {_≾_ = _≾_} a (b ∷ v) = a ≾ b

  -- Great! Now lets see how we could build a strictly ordered natural number vector.
  test : Vector ℕ (_<_) 2
  test = (1 ∷ (2 ∷ []) {tt}) {s≤s (s≤s z≤n)}
  
  -- Now regarding the first question, which is about proving that for a Vector
  -- indexed by the bottom relation the only possible vector is the empty one,
  -- we know our intuition was flawed and that requiring a proof for the singleton
  -- case is too restrictive. Hence our question needs to be reformulated:
  absurd-has-length-<2 : ∀ {n : ℕ} → Vector ℕ (λ _ _ → ⊥) n → n < 2
  absurd-has-length-<2 [] = s≤s z≤n
  absurd-has-length-<2 (a ∷ []) = s≤s (s≤s z≤n)

  -- So far so good. Now onto the next question. Can we write a sorting algorithm?
  -- Let's start with something on naturals and then see if we can generalize.

  -- I am thinking about a merge or quicksort, but for that we need to be able to split
  -- the vector in half in each recursive step. For that we need some auxiliary functions:

  -- First some conversion functions. These all need to be declared in a mutual recursive fashion.
  -- So signature first and only then the implementation.
  --
  -- Something to note is that the order in which we define the signatures is the order by which
  -- we need to define the implementation. 

  -- Oh no, I hitted a wall. It seems, I am not able to pass the needed proof obligation.
  -- And all this mutual recursive machinery is very cumbersome to deal with.
  -- It feels like I should be able to prove this but I guess I just havee to trust Agda on this
  -- one.
  -- vector₁-to-vector₂ : ∀ {ℓ} {n} {A} {_≾_} → Vectorᵐ₁ {ℓ} A _≾_ n → Vectorᵐ₂ {ℓ} A _≾_ n
  -- vector₂-to-vector₁ : ∀ {ℓ} {n} {A} {_≾_} → Vectorᵐ₂ {ℓ} A _≾_ n → Vectorᵐ₁ {ℓ} A _≾_ n
  --
  -- proof-≾₁-to-proof-≾₂ : ∀ {ℓ} {n} {A} {_≾_} (a : A) (v : Vectorᵐ₁ {ℓ} A _≾_ n)
  --                      → proof-≾₁ a v
  --                      → proof-≾₂ a (vector₁-to-vector₂ v)
  -- proof-≾₂-to-proof-≾₁ : ∀ {ℓ} {n} {A} {_≾_} (a : A) (v : Vectorᵐ₂ {ℓ} A _≾_ n)
  --                      → proof-≾₂ a v
  --                      → proof-≾₁ a (vector₂-to-vector₁ v)
  --
  --
  -- These lemmas would be useful to have but since I am not able to provide them, it means I must
  -- change my data type formulation again...
  --
  -- vector₁-to-vector₂ [] = []
  -- vector₁-to-vector₂ ((a ∷ v) {p}) = (a ∷ vector₂-to-vector₁ v) {proof-≾₂-to-proof-≾₁ a v p}
  -- 
  -- vector₂-to-vector₁ [] = []
  -- vector₂-to-vector₁ ((a ∷ v) {p}) = (a ∷ vector₁-to-vector₂ v) {proof-≾₁-to-proof-≾₂ a v p}
  -- 
  -- proof-≾₁-to-proof-≾₂ a [] p = tt
  -- proof-≾₁-to-proof-≾₂ a (a₁ ∷ v) p = p
  -- 
  -- proof-≾₂-to-proof-≾₁ a [] p = tt
  -- proof-≾₂-to-proof-≾₁ a (a₁ ∷ v) p = p
  --
  -- vector₂₁-to-vector : ∀ {ℓ} {n} {A} {_≾_} (v : Vector {ℓ} A _≾_ n)
  --                    → vector₂-to-vector₁ (vector₁-to-vector₂ v) ≡ v
  -- vector₁₂-to-vector : ∀ {ℓ} {n} {A} {_≾_} (v : Vectorᵐ₂ {ℓ} A _≾_ n)
  --                    → vector₁-to-vector₂ (vector₂-to-vector₁ v) ≡ v
  --
  --
  -- vector₂₁-to-vector [] = refl
  -- vector₂₁-to-vector ((a ∷ v) {p}) = cong (λ v′ → (a ∷ v′) {{!!}}) (vector₁₂-to-vector v)
  --
  -- vector₁₂-to-vector [] = refl
  -- vector₁₂-to-vector ((a ∷ v) {p}) = cong (λ v′ → (a ∷ v′) {{!!}}) (vector₂₁-to-vector v)


module Attempt3 where

  open Unit
  open import Data.Maybe
  open import Data.Nat.Properties
  open import Data.Bool.Base using (T)

  -- For my third attempt I am just going to leverage the mutual recursive notation I learned
  -- And define an inductive data type that tries to merge the best of both attempts.
  -- Basically one that has the same proof obligation strategy and that is allow us to simplify things.


  -- I start by defining my Vector data type with the same type signature as the previous attempts
  data Vector {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → Set ℓ

  -- And also define the signature for me proof obligation function. This function should behave in
  -- the same way it did for the previous attempt.
  proof-≾ : ∀ {ℓ} {n} {A} {_≾_} → A → Vector {ℓ} A _≾_ n → Set ℓ

  -- So now our Vector data type and proof obligation function look much simpler.
  data Vector A _≾_ where
    []  : Vector A _≾_ 0
    _∷_ : ∀ {n} (a : A) (v : Vector A _≾_ n) → {a≾b : proof-≾ a v} → Vector A _≾_ (1 + n)

  proof-≾ a [] = ⊤
  proof-≾ {_≾_ = _≾_} a (b ∷ _) = a ≾ b

  -- Lets do our first tests drives:
  test : Vector ℕ (_<_) 2
  test = (1 ∷ (2 ∷ []) {tt}) {s≤s (s≤s z≤n)}
  
  absurd-has-length-<2 : ∀ {n : ℕ} → Vector ℕ (λ _ _ → ⊥) n → n < 2
  absurd-has-length-<2 [] = s≤s z≤n
  absurd-has-length-<2 (a ∷ []) = s≤s (s≤s z≤n)

  -- Aparentely everything looks good! So let's pursue our quest of writing the sorting algorithm
  -- one more time!

  head : ∀ {ℓ} {n} {A} {_≾_}
       → Vector {ℓ} A _≾_ (1 + n)
       → A
  head (a ∷ v) = a

  tail : ∀ {ℓ} {n} {A} {_≾_}
       → Vector {ℓ} A _≾_ (1 + n)
       → Vector {ℓ} A _≾_ n
  tail (a ∷ v) = v

  last : ∀ {ℓ} {n} {A} {_≾_}
       → Vector {ℓ} A _≾_ (1 + n)
       → A
  last (a ∷ []) = a
  last (a ∷ v@(_ ∷ _)) = last v


  vector-shuffle₀ : ∀ {ℓ} {n} {A} {_≾_}
      → Vector {ℓ} A _≾_ n
      → Vector {ℓ} A _≾_ (n + 0)
  proof-vector-shuffle₀ : ∀ {ℓ} {n} {A} {_≾_}
       → (a : A)
       → (v : Vector {ℓ} A _≾_ n)
       → proof-≾ a v 
       → proof-≾ a (vector-shuffle₀ v)

  vector-shuffle₀ [] = []
  vector-shuffle₀ ((a ∷ v) {p}) = (a ∷ vector-shuffle₀ v) {proof-vector-shuffle₀ a v p}

  proof-vector-shuffle₀ _ [] _ = tt
  proof-vector-shuffle₀ _ (_ ∷ _) p = p

  vector-shuffle₁ : ∀ {ℓ} {n} {A} {_≾_}
      → Vector {ℓ} A _≾_ (1 + n)
      → Vector {ℓ} A _≾_ (n + 1)
  proof-vector-shuffle₁ : ∀ {ℓ} {n} {A} {_≾_}
       → (a : A)
       → (v : Vector {ℓ} A _≾_ (1 + n))
       → proof-≾ a v 
       → proof-≾ a (vector-shuffle₁ v)

  vector-shuffle₁ {_} {zero} ((a ∷ []) {p}) = a ∷ []
  vector-shuffle₁ {_} {suc n} ((a ∷ v) {p}) = (a ∷ vector-shuffle₁ {_} {n} v) {proof-vector-shuffle₁ a v p}

  proof-vector-shuffle₁ {_} {zero} a (b ∷ []) p = p
  proof-vector-shuffle₁ {_} {suc n} a (b ∷ v) p = p

  vector-shuffle : ∀ {ℓ} {m n} {A} {_≾_}
      → Vector {ℓ} A _≾_ (1 + (m + n))
      → Vector {ℓ} A _≾_ (m + (1 + n))
  proof-vector-shuffle : ∀ {ℓ} {m n} {A} {_≾_}
       → (a : A)
       → (v : Vector {ℓ} A _≾_ (1 + (m + n)))
       → proof-≾ a v 
       → proof-≾ a (vector-shuffle {ℓ} {m} {n} v)

  vector-shuffle {_} {zero} ((a ∷ v) {p}) = (a ∷ v) {p}
  vector-shuffle {ℓ} {suc m} ((a ∷ v) {p}) = (a ∷ vector-shuffle v) {proof-vector-shuffle {ℓ} {m} a v p}

  proof-vector-shuffle {_} {zero} _ (_ ∷ _) p = p
  proof-vector-shuffle {_} {suc m} _ (_ ∷ _) p = p

  -- append : ∀ {m n} {ℓ} {A} {_≾_}
  --            {total : Total _≾_}
  --        → Vector {ℓ} A _≾_ m
  --        → Vector {ℓ} A _≾_ n
  --        → Vector {ℓ} A _≾_ (m + n) 
  --
  -- Appending two polymorphic refined vectors is proving super hard, so I am
  -- going to first try and implement it on Nats and see how/if is going to
  -- work out. And then hopeefully will gather enough insights to generalize it
  -- later.

  -- First some insights about my attempts to define polymorphic append:
  --   - Due to the indexed length I have to do some shuffling around. This is
  --     not troublesome, but the shuffling ends up having to be done with the
  --     relational proof as well.
  --   - I think most of the troubles come from allowing polymorphic relations,
  --     and getting the weakest relational properties needed to get working.
  --     So definitely I am not specifying append correctly.
  --   - I didn't go through the trouble of setting up some examples and ended
  --     up finding obstacles that coincided with counterexamples regarding my
  --     intuition on how things should work.
  --   - Only after going through some examples I got enlightned about the
  --     obstacles Agda was giving me:
  -- 
  --   Imagine I want to append [a b c] ++ [d e f] and have the following Total
  --   relation _≾_:
  --   By construction we have: a ≾ b ≾ c and d ≾ e ≾ f
  --   So we specify the other relations: 
  --    f ≾ a, f ≾ b, f ≾ c
  --    e ≾ a, e ≾ b, e ≾ c
  --    a ≾ d, d ≾ b, d ≾ c
  --
  --   Then: [a b c] ++ [d e f] =
  --
  --    a ≾ d ? yes
  --    
  --    a : [b c] ++ [d e f]
  --    
  --    b ≾ d ? no
  --    
  --    a : d : [b c] ++ [e f] !!! Requires that a ≾ d and that is not true
  -- 
  -- 
  id-≤  : ∀ m → m ≤ m
  id-≤ zero = z≤n
  id-≤ (suc m) = s≤s (id-≤ m)

  minimum² : ∀ {m n} {total : Total _≤_}
           → (as : Vector ℕ _≤_ (1 + m))
           → (bs : Vector ℕ _≤_ (1 + n))
           → ℕ
  minimum² {total = total} (a ∷ as) (b ∷ bs) with total a b
  ... | inj₁ a≤b = a 
  ... | inj₂ b≤a = b

  append-ℕ : ∀ {m n} {total : Total _≤_}
           → (as : Vector ℕ _≤_ m)
           → (bs : Vector ℕ _≤_ n)
           → Vector ℕ _≤_ (m + n)
  append-ℕ-aux : ∀ {m n r} {total : Total _≤_}
               → (a : ℕ)
               → (as : Vector ℕ _≤_ m)
               → (bs : Vector ℕ _≤_ n)
               → proof-≾ r (append-ℕ as bs) 

  -- splitAt : ∀ m {n} {A} {_≾_} (xs : Vector A _≾_ (m + n)) →
  --           ∃₂ λ (ys : Vector A _≾_ m) (zs : Vector A _≾_ n) → xs ≡ ys ++ zs
  -- splitAt zero    xs                = ([] , xs , refl)
  -- splitAt (suc m) (x ∷ xs)          with splitAt m xs
  -- splitAt (suc m) (x ∷ .(ys ++ zs)) | (ys , zs , refl) =
  --   ((x ∷ ys) , zs , refl)

  -- sort : ∀ {n : ℕ} {_≾_ : Rel ℕ _} -> Vector ℕ (_≾_) n -> Vector ℕ (_≤_) n
  -- sort {n} v = {!!}
