# Refined Sorted Vector

I have been sitting on this idea for a while: What could I possible do with a refined v
data structure that could give me some guarantees about the order of its elements?

I had two questions in mind:
  - Would I be able to prove that a v indexed by the bottom
    relation (i.e. no two elements are related) has length 0 ?
  - Can I write a sorting algorithm the goes from a v with an arbitrary relation to
    one that is ordered?

What more questions could I ask? If it worked then this data type index's would represent
a form of refinement types withing the data structure itself that would allow us to have
correct-by-construction code and also we could aid the compiler to leverage about all information
and have machine-checked proofs about our code.

In this literate Agda file I document my journey and any successes and failures a long the way.

```agda
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
```

At some point we will need this custom, universe polymorphic `Unit` type.

```agda
module Unit where

  record ⊤ {ℓ : Level} : Set ℓ where
    instance constructor tt
```

## First Attempt

This is the first attempt where I naively try to express in Agda what I initially had in mind
for this idea.

```agda
module Attempt1 where
```

This is the definition I first had in mind. A Vector indexed by natural numbers (the length)
and by an arbitrary homogeneous binary relation (the order of the elements in the v).

```agda
  data Vector {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → Set ℓ where
```

The empty case constructor is simple, we do not require any proofs using the order
Because there are no elements to compare.

```agda
    []      : Vector A _≾_ 0
```

This is the singleton list case. We have it because the cons constructor for this data type
receives 2 elements instead of the standard 1, and I wanted to be able to represent any length
vectors. I am a bit uneasy about my choice here but I had to require some relation with this
singleton element and I picked the reflexive one. Lets hope it doesn't bite me in the future.

```agda
    [_]     : ∀ (x : A) {x≾y : x ≾ x} → Vector A _≾_ 1
```
This is where the magic happens. This 2-cons constructor receives 2 elements to cons to a given
v, but also needs a proof about their order.

```agda
    _∷_∷_ : ∀ {n : ℕ} (x : A) (y : A) (xs : Vector A _≾_ n) {x≾y : x ≾ y} → Vector A _≾_ (2 + n)
```

Great! Now lets see how we could build a strictly ordered natural number vector:

```agda
  test : Vector ℕ (_<_) 2
  test = (1 ∷ 2 ∷ []) {s≤s (s≤s z≤n)}
```

Now lets see if we can answer the first question, which is about proving that for a Vector
indexed by the bottom relation the only possible vector is the empty one.

```agda
  absurd-has-length-0 : ∀ {n : ℕ} → Vector ℕ (λ _ _ → ⊥) n → n ≡ 0
  absurd-has-length-0 [] = refl
```

Awesome! Agda managed to prove it just with `refl`, that's the kind of power I was looking
to provide to the compiler with a data structure formulation like this.

Now lets see if we can prove (code) that sorting a ℕ's Vector indexed by an
arbitrary relation, results in an ordered list.

I am thinking about a mergesort or quicksort, but for that we need to be able to split
the v in half in each recursive step, and to merge them together.

First lets try to define some simple functions and see if we are able to do so.
If it turns out it is very difficult or even impossible, then maybe we are not
in the right track.

The head function is relatively straightforward:

```agda
  head : ∀ {n} {ℓ} {A} {_≾_} → Vector {ℓ} A _≾_ (1 + n) → A
  head [ x ]       = x
  head (x ∷ _ ∷ _) = x
```

It appears that head's counterpart function - tail, is not straightforward due to
the way our data constructors are designed. In order to implement tail I need some
auxiliary function that lets me cons just a single element into a vector.

The challenge here is providing the actual proof that the element I want to cons respects
the order, because we can either be cons-ing the element to an empty list or a non-empty
list. In simpler terms, we either need to provide a reflexive proof or a proof that
the element that we want to add relates with the head of the non-empty vector.

Coming with a suitable, ergonomic type signature was hard, but ultimately I found this one
where one passes a function that computes the proof for us, for an arbitrary value.

```agda
  cons : ∀ {n} {ℓ} {A} {_≾_ : Rel A ℓ}
       → (a : A)
       → Vector {ℓ} A _≾_ n
       -> ((b : A) → a ≾ b )
       → Vector {ℓ} A _≾_ (1 + n)
  cons a [] f = [ a ] {f a}
  cons a [ x ] f = (a ∷ x ∷ []) {f x}
  cons a (x ∷ y ∷ v) f = (a ∷ y ∷ cons a v f) {f y}
```

This is my miserable attempt to define the tail function on refined vectors. I thought
I needed the cons function but it appears I can not produce the proof I need so easily.

While trying to define tail I discovered a major flaw on my data type which is I can only
enforce the order in a non-transitive way. E.g. the vector `[1, 2, 0, 1]` would be valid, because
I do not require any proof between 2 and 0.

```agda
-- tail : ∀ {n} {A} {_≾_} {reflexive : Reflexive _≾_}
--      → Vector A _≾_ (1 + n)
--      → Vector A _≾_ n
-- tail [ x ]       = []
-- tail {reflexive = reflexive} (x ∷ y ∷ v) with v
-- ... | [] = [ y ] {reflexive {y}}
-- ... | [ z ] = (y ∷ z ∷ []) {{!!}}
-- ... | x₁ ∷ y₁ ∷ res = {!!}
```

I need to reformulate my data type.

## Second Attempt

```agda
module Attempt2 where
```

We need to roll our own `⊤` data type, for reasons enumerated below.

```agda
  open Unit
```

After much thinking I think I can maybe fix my problem with a mutual recursive data type.
Here's what I thought about:

Two refined vector types, and in Agda if I want to define mutual recursive data types
I have to provide the type signature first and only then the constructor declarations

```agda
  data Vectorᵐ₁ {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → Set ℓ
  data Vectorᵐ₂ {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → Set ℓ
```

One wrapper to normalise the API

```agda
  Vector : {ℓ : Level} → (A : Set ℓ) → Rel A ℓ → ℕ → Set ℓ
  Vector A _≾_ n = Vectorᵐ₁ A _≾_ n
```

My two Vector types are going to have only a cons constructor and not a 2-cons constructor.
These head functions take the parameters of the cons constructor and either outputs the head
of the list if it is non-empty or just returns the element to cons.

This is needed to calculate which type of proof one needs to give. If we are consing something
to the empty list we need to provide a reflexive proof, otherwise a relation proof. As we are
going to see below.

**NOTE**: We have to declare these functions in the same way we are doing for our recursive types
because we are going to have to include them in the data declarations.

Deprecated reason:

It appears that requiring a reflexive proof is too restrictive. We should ditch
that.

```agda
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
```

My two Vector types are going to have only a cons constructor and not a 2-cons constructor.
These `proof-≾` functions take the parameters of the cons constructor and output the required
order proof obligation. If the list is empty we do not require any proof obligation as doing so
would be too restrictive (read above). If the list is non-empty we require a proof obligation
that `a ≾ head v`.

```agda
  proof-≾₁ : ∀ {ℓ} {n} {A} {_≾_} → A → Vectorᵐ₁ {ℓ} A _≾_ n → Set ℓ
  proof-≾₂ : ∀ {ℓ} {n} {A} {_≾_} → A → Vectorᵐ₂ {ℓ} A _≾_ n → Set ℓ
```

As mentioned above our `Vectorᵐ` types are mutually recursive. Both have an empty list constructor
and a cons constructor. The cons constructor receives the element to cons, a list of the opposite
type, either `Vectorᵐ₁` or `Vectorᵐ₂`, and a proof that the element we want to cons respects the order
given the result of `headₐ`, which as I explained above will be either `a ≾ a` or `a ≾ head v` .

```agda
  data Vectorᵐ₁ {ℓ} A _≾_ where
    []  : Vectorᵐ₁ A _≾_ 0
    _∷_ : ∀ {n} (a : A) (v : Vectorᵐ₂ A _≾_ n) → {a≾b : proof-≾₂ {ℓ} {n} {A} {_≾_} a v} → Vectorᵐ₁ A _≾_ (1 + n)

  data Vectorᵐ₂ {ℓ} A _≾_ where
    []  : Vectorᵐ₂ A _≾_ 0
    _∷_ : ∀ {n} (a : A) (v : Vectorᵐ₁ A _≾_ n) → {a≾b : proof-≾₁ {ℓ} {n} {A} {_≾_} a v} → Vectorᵐ₂ A _≾_ (1 + n)
```

Finally we define the body of `proof-≾` here. Notice the overloading of the constructor operators!
In the empty list case we realise that ⊤ from Data.Unit is not universe polymorphic so we need to
roll our own.

```agda
  proof-≾₁ _ [] = ⊤
  proof-≾₁ {_≾_ = _≾_} a (b ∷ v) = a ≾ b

  proof-≾₂ _ [] = ⊤
  proof-≾₂ {_≾_ = _≾_} a (b ∷ v) = a ≾ b
```

Great! Now lets see how we could build a strictly ordered natural number vector.

```agda
  test : Vector ℕ (_<_) 2
  test = (1 ∷ (2 ∷ []) {tt}) {s≤s (s≤s z≤n)}
```

Now regarding the first question, which is about proving that for a Vector
indexed by the bottom relation the only possible vector is the empty one,
we know our intuition was flawed and that requiring a proof for the singleton
case is too restrictive. Hence our question needs to be reformulated:

```agda
  absurd-has-length-<2 : ∀ {n : ℕ} → Vector ℕ (λ _ _ → ⊥) n → n < 2
  absurd-has-length-<2 [] = s≤s z≤n
  absurd-has-length-<2 (a ∷ []) = s≤s (s≤s z≤n)
```

So far so good. Now onto the next question. Can we write a sorting algorithm?
Let's start with something on naturals and then see if we can generalize.

I am thinking about a append or quicksort, but for that we need to be able to split
the vector in half in each recursive step. For that we need some auxiliary functions:

First some conversion functions. These all need to be declared in a mutual recursive fashion.
So signature first and only then the implementation.

Something to note is that the order in which we define the signatures is the order by which
we need to define the implementation.

Oh no, I hit a wall. It seems, I am not able to pass the needed proof obligation.
And all this mutual recursive machinery is very cumbersome to deal with.
It feels like I should be able to prove this but I guess I just have to trust Agda on this
one.

```agda
  -- v₁-to-v₂ : ∀ {ℓ} {n} {A} {_≾_} → Vectorᵐ₁ {ℓ} A _≾_ n → Vectorᵐ₂ {ℓ} A _≾_ n
  -- v₂-to-v₁ : ∀ {ℓ} {n} {A} {_≾_} → Vectorᵐ₂ {ℓ} A _≾_ n → Vectorᵐ₁ {ℓ} A _≾_ n
  --
  -- proof-≾₁-to-proof-≾₂ : ∀ {ℓ} {n} {A} {_≾_} (a : A) (v : Vectorᵐ₁ {ℓ} A _≾_ n)
  --                      → proof-≾₁ a v
  --                      → proof-≾₂ a (v₁-to-v₂ v)
  -- proof-≾₂-to-proof-≾₁ : ∀ {ℓ} {n} {A} {_≾_} (a : A) (v : Vectorᵐ₂ {ℓ} A _≾_ n)
  --                      → proof-≾₂ a v
  --                      → proof-≾₁ a (v₂-to-v₁ v)
  --
```
These lemmas would be useful to have but since I am not able to provide them, it means I must
change my data type formulation again...

```agda
  -- v₁-to-v₂ [] = []
  -- v₁-to-v₂ ((a ∷ v) {p}) = (a ∷ v₂-to-v₁ v) {proof-≾₂-to-proof-≾₁ a v p}
  --
  -- v₂-to-v₁ [] = []
  -- v₂-to-v₁ ((a ∷ v) {p}) = (a ∷ v₁-to-v₂ v) {proof-≾₁-to-proof-≾₂ a v p}
  --
  -- proof-≾₁-to-proof-≾₂ a [] p = tt
  -- proof-≾₁-to-proof-≾₂ a (a₁ ∷ v) p = p
  --
  -- proof-≾₂-to-proof-≾₁ a [] p = tt
  -- proof-≾₂-to-proof-≾₁ a (a₁ ∷ v) p = p
  --
  -- v₂₁-to-v : ∀ {ℓ} {n} {A} {_≾_} (v : Vector {ℓ} A _≾_ n)
  --                    → v₂-to-v₁ (v₁-to-v₂ v) ≡ v
  -- v₁₂-to-v : ∀ {ℓ} {n} {A} {_≾_} (v : Vectorᵐ₂ {ℓ} A _≾_ n)
  --                    → v₁-to-v₂ (v₂-to-v₁ v) ≡ v
  --
  --
  -- v₂₁-to-v [] = refl
  -- v₂₁-to-v ((a ∷ v) {p}) = cong (λ v′ → (a ∷ v′) {{!!}}) (v₁₂-to-v v)
  --
  -- v₁₂-to-v [] = refl
  -- v₁₂-to-v ((a ∷ v) {p}) = cong (λ v′ → (a ∷ v′) {{!!}}) (v₂₁-to-v v)
```

## Third Attempt

```agda
module Attempt3 where

  open Unit
  open import Data.Maybe
  open import Data.Nat.Properties
  open import Data.Bool.Base using (T)
```

For my third attempt I am just going to leverage the mutual recursive notation I learned
and define an inductive data type that tries to append the best of both attempts.
Basically one that has the same proof obligation strategy and that allow us to simplify things.

I start by defining my Vector data type with the same type signature as the previous attempts

```agda
  data Vector {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → Set ℓ
```

And also define the signature for me proof obligation function. This function should behave in
the same way it did for the previous attempt.

```agda
  proof-≾ : ∀ {ℓ} {n} {A} {_≾_} → A → Vector {ℓ} A _≾_ n → Set ℓ
```

So now our Vector data type and proof obligation function look much simpler.

```agda
  data Vector A _≾_ where
    []  : Vector A _≾_ 0
    _∷_ : ∀ {n} (a : A) (v : Vector A _≾_ n) → {a≾b : proof-≾ a v} → Vector A _≾_ (1 + n)

  proof-≾ a [] = ⊤
  proof-≾ {_≾_ = _≾_} a (b ∷ _) = a ≾ b
```

Lets do our first tests drives:

```agda
  test : Vector ℕ (_<_) 2
  test = (1 ∷ (2 ∷ []) {tt}) {s≤s (s≤s z≤n)}

  absurd-has-length-<2 : ∀ {n : ℕ} → Vector ℕ (λ _ _ → ⊥) n → n < 2
  absurd-has-length-<2 [] = s≤s z≤n
  absurd-has-length-<2 (a ∷ []) = s≤s (s≤s z≤n)
```

Apparently everything looks good! So let's pursue our quest of writing the sorting algorithm
one more time!

First some sanity test that we are able to implement some simple functions over
our data type:

```agda
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
```

Great! Now let's tackle one piece of the puzzle, the merge function.
When dealing with lists or non-indexed vectors, a common
operation to have is the append function that appends two lists/vectors
together. Another common one is the merge function that given two lists
of sortable elements, we are able to merge the lists together in a sorted
manner. Curiously the append for our refined vector data type has to
preserve the order as well which means that for this particular data type
the append is actually the merge function, since there's only one way we
can append two vectors preserving their relation (by merging the)!

Here we define some auxiliary number shuffling functions:

```agda
  v-shuffle₀ : ∀ {ℓ} {n} {A} {_≾_}
      → Vector {ℓ} A _≾_ n
      → Vector {ℓ} A _≾_ (n + 0)
  proof-≾-shuffle₀ : ∀ {ℓ} {n} {A} {_≾_}
       → (a : A)
       → (v : Vector {ℓ} A _≾_ n)
       → proof-≾ a v
       → proof-≾ a (v-shuffle₀ v)

  v-shuffle₀ [] = []
  v-shuffle₀ ((a ∷ v) {p}) = (a ∷ v-shuffle₀ v) {proof-≾-shuffle₀ a v p}

  proof-≾-shuffle₀ _ [] _ = tt
  proof-≾-shuffle₀ _ (_ ∷ _) p = p

  v-shuffle₁ : ∀ {ℓ} {n} {A} {_≾_}
      → Vector {ℓ} A _≾_ (1 + n)
      → Vector {ℓ} A _≾_ (n + 1)
  proof-≾-shuffle₁ : ∀ {ℓ} {n} {A} {_≾_}
       → (a : A)
       → (v : Vector {ℓ} A _≾_ (1 + n))
       → proof-≾ a v
       → proof-≾ a (v-shuffle₁ v)

  v-shuffle₁ {_} {zero} ((a ∷ []) {p}) = a ∷ []
  v-shuffle₁ {_} {suc n} ((a ∷ v) {p}) = (a ∷ v-shuffle₁ {_} {n} v) {proof-≾-shuffle₁ a v p}

  proof-≾-shuffle₁ {_} {zero} a (b ∷ []) p = p
  proof-≾-shuffle₁ {_} {suc n} a (b ∷ v) p = p

  v-shuffle : ∀ {ℓ} {m n} {A} {_≾_}
      → Vector {ℓ} A _≾_ (1 + (m + n))
      → Vector {ℓ} A _≾_ (m + (1 + n))
  proof-≾-shuffle : ∀ {ℓ} {m n} {A} {_≾_}
       → (a : A)
       → (v : Vector {ℓ} A _≾_ (1 + (m + n)))
       → proof-≾ a v
       → proof-≾ a (v-shuffle {ℓ} {m} {n} v)

  v-shuffle {_} {zero} ((a ∷ v) {p}) = (a ∷ v) {p}
  v-shuffle {ℓ} {suc m} ((a ∷ v) {p}) = (a ∷ v-shuffle v) {proof-≾-shuffle {ℓ} {m} a v p}

  proof-≾-shuffle {_} {zero} _ (_ ∷ _) p = p
  proof-≾-shuffle {_} {suc m} _ (_ ∷ _) p = p
```

Appending two polymorphic refined vs is proving super hard, so I am
going to first try and implement it on Nats and see how/if is going to
work out. And then hopefully will gather enough insights to generalize it
later.

```agda
  -- append : ∀ {m n} {ℓ} {A} {_≾_}
  --            {total : Total _≾_}
  --        → Vector {ℓ} A _≾_ m
  --        → Vector {ℓ} A _≾_ n
  --        → Vector {ℓ} A _≾_ (m + n)
```

First some insights about my attempts to define polymorphic append:
  - Due to the indexed length I have to do some shuffling around. This is
    not troublesome, but the shuffling ends up having to be done with the
    relational proof as well.
  - I think most of the troubles come from allowing polymorphic relations,
    and getting the weakest relational properties needed to get working.
  - I didn't go through the trouble of setting up some examples and ended
    up finding obstacles that coincided with counterexamples regarding my
    intuition on how things should work.
  - Only after going through some examples I got enlightened about the
    obstacles Agda was giving me:

It seems that specializing to Nats helps a little bit and makes it clearer
why Agda does not like what I am trying to do.

```agda
  -- append-ℕ : ∀ {m n} {total : Total _≤_}
  --          → (as : Vector ℕ _≤_ m)
  --          → (bs : Vector ℕ _≤_ n)
  --          → Vector ℕ _≤_ (m + n)
```

It seems that due the way my data type is designed (`proof-≾` mentions the Vector
data type and vice versa), in the recursive case of the append function, I ended
up with something like this in my goal:

`_a≾b_409 : proof-≾ a (append-ℕ-aux as (b ∷ bs))a`

Because `proof-≾` has a `v` (Vector) as its second argument you end up with the recursive
call the goal, which is tricky (perhaps impossible) to deal with.

So I guess this means I should figure out a better, clever way to design the
data structure in such a way that does not give Agda such a bad time.

## Fourth Attempt

```agda
module Attempt4 where

  open import Data.Nat.Properties using (+-comm; +-identityʳ)
```

Thanks to my friend Sean Seefried, he found the following [paper](http://www.e-pig.org/downloads/ydtm.pdf).

Section 5.2 from the paper is exactly what I am after. And from reading it they offer
a great deal of insight on how to think about problems like these.
Their idea, although specialized to ℕ and restricted to Total orders, is to index
the Vector type by bounds as well. Which makes sense and it is this little bit of intrinsic
evidence that makes Agda able to get through the recursive step on append.

Let me show case what they suggest in the paper:

The only difference here is that we require a `Total` constraint on the order
and we also index by and arbitrary element of type `A` (the lower bound).
This lower bound means that the Vector shall only contain values greater or equal than
it.

```agda
  data Vector {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) (t : Total _≾_) : ℕ → A → Set ℓ where
```
The empty vector case does not care what the lower bound is

```agda
    [] : {lb : A} → Vector A _≾_ t 0 lb
```

In cons case, the head must exceed the prescribed lower bound and bound the tail in turn.
This means `lb` is an open bound.

```agda
    _∷_ : {lb : A} {n : ℕ} → (a : A) → {lb ≾ a} → Vector A _≾_ t n a → Vector A _≾_ t (suc n) lb
```

Some examples:

```agda
  ≤-total : Total _≤_
  ≤-total zero zero = inj₁ z≤n
  ≤-total zero (suc y) = inj₁ z≤n
  ≤-total (suc x) zero = inj₂ z≤n
  ≤-total (suc x) (suc y) with ≤-total x y
  ... | inj₁ x≤y = inj₁ (s≤s x≤y)
  ... | inj₂ y≤x = inj₂ (s≤s y≤x)

  example1 : Vector ℕ _≤_ ≤-total 3 0
  example1 = _∷_ 0 {z≤n} (_∷_ 3 {z≤n} (_∷_ 5 {s≤s (s≤s (s≤s z≤n))} []))

  example2 : Vector ℕ _≤_ ≤-total 3 0
  example2 = _∷_ 2 {z≤n} (_∷_ 4 {s≤s (s≤s z≤n)} (_∷_ 6 {s≤s (s≤s (s≤s (s≤s z≤n)))} []))
```

Now in the paper, I think they simplify the merge (append) function type signature by requiring
that the two vectors share the same lower bound, so the result also shares it. I think we might be able
to get away with being a little more general, but we will let Agda be the judge of that.
Here's the definition of append:

```agda
  head : ∀ {ℓ} {A} {b : A} {n : ℕ} {_≾_} {total : Total _≾_}→ Vector {ℓ} A _≾_ total (suc n) b → A
  head (a ∷ _) = a

  suc-m+n≡m+suc-n : ∀ (m n : ℕ) → (suc m + n) ≡ (m + suc n)
  suc-m+n≡m+suc-n m n rewrite +-comm m n rewrite +-comm (suc n) m = refl

  vec2vec : ∀ {ℓ} {A : Set ℓ} {_≾_ : Rel A ℓ} {total : Total _≾_} {b : A} {m n : ℕ} → Vector A _≾_ total (suc m + n) b → Vector A _≾_ total (m + suc n) b
  vec2vec {A = A} {_≾_} {total} {b} {m} {n} v rewrite cong (λ n → Vector A _≾_ total n b) (suc-m+n≡m+suc-n m n) = v

  append : ∀ {ℓ} {A} {m n : ℕ} {_≾_} {total : Total _≾_}→ {b : A}
        → Vector {ℓ} A _≾_ total m b
        → Vector {ℓ} A _≾_ total n b
        → Vector {ℓ} A _≾_ total (m + n) b
  append {m = zero} _ bs = bs
  append {m = m} {zero} as _ rewrite +-identityʳ m = as
  append {A = A} {_≾_ = _≾_} {total = total} {b}  (_∷_ x {b≾x} xs ) (_∷_ y {b≾y} ys) with total x y
  ... | inj₁ x≾y = _∷_ x {b≾x} (append {b = x}  xs (_∷_ y {x≾y} ys))
  ... | inj₂ y≾x = _∷_ y {b≾y} (vec2vec  (append {b = y} (_∷_ x {y≾x} xs) ys))
```

If I C-c C-n inside this hole I get the correct result!

```agda
  -- example3 : Vector ℕ _≤_ ≤-total 6 0
  -- example3 = {! append example1 example2 !}
```

As I said above I do not understand why the append function, in the paper needs the 2 vectors to
share the lower bound, that seems oddly restrictive, it should be possible to append 2 vectors of
arbitrary bounds and then the result type would have the minimum between the two. Looks reasonable,
right? Another thing I wonder is that we might get away without passing Total in the data type,
I like it much more we you could keep everything polymorphic and then require Total for append,
for example.

Another thing I noticed is that their sorting proof besides being tied to ℕ is also a bit different
than what I would expect. What I want is a general sorting function that given a Vector indexed
by an arbitrary `_≾_` relation, returns a new one indexed by a different one. Is it possible? I don't
really know, but it seems a nice guess. Probably the output relation needs to have stronger properties
like being an Equivalence relation, we'll see!

Let's try that in attempt 5!

## Fith Attempt

```agda
module Attempt5 where

  open Unit
```

Now there are several changes I want to make to the data type. The first one,
is to not require the Total constraint on the relation. The second one is that I
want a closed bound on my data type. The closed bound idea seems closer to my previous
definitions and I want to experiment with it. From reading the paper they said for more
complex functions we might actually need a upper bound, which makes sense to me, but let's
leave that out of the equation for now.

```agda
  proof-≾ : ∀ {ℓ} {A : Set ℓ} {_≾_ : Rel A ℓ} → (n : ℕ) → (a lb : A) → Set ℓ
  proof-≾ {ℓ} zero a lb = ⊤
  proof-≾ {_≾_ = _≾_} (suc n) a lb = a ≾ lb
```

```agda
  data Vector {ℓ : Level} (A : Set ℓ) (_≾_ : Rel A ℓ) : ℕ → A → Set ℓ where
```
As previous, the empty vector case does not care what the lower bound is

```agda
    [] : {lb : A} → Vector A _≾_ 0 lb
```

In cons case, the head must be smaller than the tail's lower bound which in turn will
make the resulting type's lower bound be the head.
This means `lb` is a closed bound.

The way this is defined means that, for example, the singleton list will need to require
_some_ proof, which is a bit disappointing. I guess this is why they went for a open bound in
the paper, but I really want this to work so I'll do one small trick. With
`proof-≾` I'll check the length of the tail vector, and if it is 0 then ask for the trivial
proof (`⊤`). Since `proof-≾` is not mutual recursive with the Vector definition I hope
this trick will work out nicely.

```agda
    _∷_ : {lb : A} {n : ℕ}
        → (a : A)
        → Vector A _≾_ n lb
        → {proof-≾ {ℓ} {A} {_≾_ = _≾_} n a lb}
        → Vector A _≾_ (suc n) a
```

Lets get some examples going:

You might notice that now copy pasting exactly the same examples from attempt 5
won't type check, that is because the head of the v needs to be the Vector's
lower bound.

```agda
  example1 : Vector ℕ _≤_ 3 0
  example1 = (0 ∷ (3 ∷ (5 ∷ [] {lb = zero})) {s≤s (s≤s (s≤s z≤n))}) {z≤n}

  example2 : Vector ℕ _≤_ 3 1
  example2 = (1 ∷ (4 ∷ (6 ∷ [] {lb = zero})) {s≤s (s≤s (s≤s (s≤s z≤n)))}) {s≤s z≤n}
```

It works! It is a shame that we have to fill so much information, but let's continue seeing
where this formulation leads us.

Next up is the append/merge function, we shall attempt to generalize the
type signature in order to accommodate any lower bound input vectors, and
return one, which lower bound is the minimum of the inputs.

Minimum between two elements that can be totally ordered. This function
also has the length of the Vector in consideration, since the empty vector
case requires any `lowerbound` we make sure that if the index is 0 then
the minimum `lowerbound` becomes that of the non-empty list.

```agda
  min : ∀ {ℓ} {A : Set ℓ} {_≾_ : Rel A ℓ} {total : Total _≾_}
      → A → A → A
  min {total = total} a b with total a b
  ... | inj₁ a≾b = a
  ... | inj₂ b≾a = b
  
  min-n : ∀ {ℓ} {A : Set ℓ} {_≾_ : Rel A ℓ} {total : Total _≾_}
      → ℕ → A
      → ℕ → A
      → A
  min-n zero _ (suc _) b = b
  min-n (suc _) a zero _ = a
  min-n {total = total} _ a _ b = min {total = total} a b
```

Vector auxiliary lemmas to shuffle around length index

```agda
  v-shuffle₀ : ∀ {ℓ} {A} {_≾_} {n} {b}
             → Vector {ℓ} A _≾_ n b
             → Vector {ℓ} A _≾_ (n + 0) b
  proof-≾-shuffle₀ : ∀ {ℓ} {A : Set ℓ} {_≾_ : Rel A ℓ} {n} {a b}
                   → proof-≾ {ℓ} {A} {_≾_} n a b
                   → proof-≾ {ℓ} {A} {_≾_} (n + 0) a b

  v-shuffle₀ [] = []
  v-shuffle₀ {n = suc n} ((a ∷ as) {p}) =
    (a ∷ (v-shuffle₀ as)) {proof-≾-shuffle₀ {n = n} p}

  proof-≾-shuffle₀ {n = zero} _ = tt
  proof-≾-shuffle₀ {n = suc _} p = p

  v-shuffle₀⁻¹ : ∀ {ℓ} {A} {_≾_} {n} {b}
             → Vector {ℓ} A _≾_ (n + 0) b
             → Vector {ℓ} A _≾_ n b
  proof-≾-shuffle₀⁻¹ : ∀ {ℓ} {A : Set ℓ} {_≾_ : Rel A ℓ} {n} {a b}
                   → proof-≾ {ℓ} {A} {_≾_} (n + 0) a b
                   → proof-≾ {ℓ} {A} {_≾_} n a b

  v-shuffle₀⁻¹ {n = zero} v = v
  v-shuffle₀⁻¹ {n = suc n} ((a ∷ v) {p}) =
    (a ∷ v-shuffle₀⁻¹ v) {proof-≾-shuffle₀⁻¹ {n = n} p}

  proof-≾-shuffle₀⁻¹ {n = zero} p = tt
  proof-≾-shuffle₀⁻¹ {n = suc n} p = p

  proof-≾-shuffle₀-id : ∀ {ℓ} {A : Set ℓ} {_≾_ : Rel A ℓ} {n} {a b}
                → (p : proof-≾ {ℓ} {A} {_≾_} (n + 0) a b)
                → proof-≾-shuffle₀ {ℓ} {A} {_≾_} {n} (proof-≾-shuffle₀⁻¹ {ℓ} {A} {_≾_} {n} p) ≡ p
  proof-≾-shuffle₀-id {n = zero} tt = refl
  proof-≾-shuffle₀-id {n = suc n} p = refl

  v-cong : ∀ {ℓ} {A : Set ℓ} {_≾_ : Rel A ℓ} {n : ℕ} {lb : A}
         → (b : A)
         → (bs : Vector {ℓ} A _≾_ (n + 0) lb)
         → (p : proof-≾ (n + 0) b lb)
         → (b ∷ v-shuffle₀ (v-shuffle₀⁻¹ bs))
           {proof-≾-shuffle₀ {n = n} (proof-≾-shuffle₀⁻¹ {n = n} p)} ≡ (b ∷ bs) {p}
  v-cong {n = zero} b [] p = refl
  v-cong {n = suc n} b ((lb ∷ bs) {p′}) p = cong (λ x → (b ∷ x) {p}) (v-cong lb bs p′)

  v-shuffle₀-id : ∀ {ℓ} {A} {_≾_} {n} {b}
                → (xs : Vector {ℓ} A _≾_ (n + 0) b)
                → v-shuffle₀ (v-shuffle₀⁻¹ xs) ≡ xs
  v-shuffle₀-id {n = zero} [] = refl
  v-shuffle₀-id {ℓ} {A} {_≾_} {n = suc n} (_∷_ {lb = lb} b bs {p} ) =
    begin
      ((b ∷ v-shuffle₀ (v-shuffle₀⁻¹ bs)) {proof-≾-shuffle₀ {n = n} (proof-≾-shuffle₀⁻¹ {n = n} p)})
      ≡⟨ v-cong b bs p ⟩
      ((b ∷ bs) {p})
    ∎
    where open ≡-Reasoning

  v-shuffle : ∀ {ℓ} {A} {_≾_} {m n} {b}
            → Vector {ℓ} A _≾_ (1 + (m + n)) b
            → Vector {ℓ} A _≾_ (m + (1 + n)) b
  proof-≾-shuffle : ∀ {ℓ} {A} {_≾_} {m n} {a b}
                  → proof-≾ {ℓ} {A} {_≾_} (1 + (m + n)) a b
                  → proof-≾ {ℓ} {A} {_≾_} (m + (1 + n)) a b

  v-shuffle {m = zero} ((a ∷ as) {p}) = (a ∷ as) {p}
  v-shuffle {m = suc m} ((a ∷ as) {p}) =
    (a ∷ (v-shuffle {m = m} as)) {proof-≾-shuffle {m = m} p}

  proof-≾-shuffle {m = zero} p = p
  proof-≾-shuffle {m = suc _} p = p

  v-shuffle⁻¹ : ∀ {ℓ} {A} {_≾_} {m n} {b}
              → Vector {ℓ} A _≾_ (m + (1 + n)) b
              → Vector {ℓ} A _≾_ (1 + (m + n)) b
  proof-≾-shuffle⁻¹ : ∀ {ℓ} {A} {_≾_} {m n} {a b}
                    → proof-≾ {ℓ} {A} {_≾_} (m + (1 + n)) a b
                    → proof-≾ {ℓ} {A} {_≾_} (1 + (m + n)) a b

  v-shuffle⁻¹ {m = zero} as = as
  v-shuffle⁻¹ {m = suc m} ((a ∷ as) {p}) = (a ∷ v-shuffle⁻¹ as) {proof-≾-shuffle⁻¹ {m = m} p}

  proof-≾-shuffle⁻¹ {m = zero} p = p
  proof-≾-shuffle⁻¹ {m = suc m} p = p

  append-aux₀ : ∀ {ℓ} {A} {_≾_} {total : Total _≾_} {m n} {a b lb : A}
         → proof-≾ {ℓ} {A} {_≾_} m a lb
         → a ≾ b
         → proof-≾ {ℓ} {A} {_≾_} (m + suc n) a (min-n {total = total} m lb (suc n) b)
  append-aux₀ {m = zero} _ p′ = p′
  append-aux₀ {total = total} {m = suc m} {b = b} {lb = lb} p p′ with total lb b
  ... | inj₁ lb≾b = p
  ... | inj₂ b≾lb = p′

  append-aux₁ : ∀ {ℓ} {A} {_≾_} {total : Total _≾_} {m n} {a b lb : A}
         → proof-≾ {ℓ} {A} {_≾_} n b lb
         → b ≾ a
         → proof-≾ {ℓ} {A} {_≾_} (m + suc n) b (min-n {total = total} (suc m) a n lb)
  append-aux₁ {m = zero} {n = zero} p p′ = p′
  append-aux₁ {m = suc m} {n = zero} p p′ = p′
  append-aux₁ {total = total} {m = zero} {n = suc n} {a = a} {lb = lb} p p′ with total a lb
  ... | inj₁ _ = p′
  ... | inj₂ _ = p
  append-aux₁ {total = total} {m = suc m} {n = suc n} {a = a} {lb = lb} p p′ with total a lb
  ... | inj₁ _ = p′
  ... | inj₂ _ = p

  append : ∀ {ℓ} {A} {_≾_} {total : Total _≾_} {m n} {b b′}
        → Vector {ℓ} A _≾_ m b
        → Vector {ℓ} A _≾_ n b′
        → Vector {ℓ} A _≾_ (m + n) (min-n {total = total} m b n b′)
  append {m = zero} {n = zero} _ _ = []
  append {m = zero} {n = suc n} _ bs = bs
  append {m = suc m} {n = zero} as _ = v-shuffle₀ as
  append {total = total} {m = suc m} {n = suc n}
        aas@((a ∷ as) {pa})
        bbs@((b ∷ bs) {pb}) with total a b
  ... | inj₁ a≾b = (a ∷ (append {total = total} as bbs)) {append-aux₀ {m = m} pa a≾b}
  ... | inj₂ b≾a = (b ∷ (v-shuffle (append {total = total} aas bs))) {append-aux₁ {m = m} pb b≾a}
```

Success! We managed to write append with our closed bounds Vector data type.
And even managed to be slightly more general on the input vector's bounds.

```agda
  ≤-total : Total _≤_
  ≤-total zero zero = inj₁ z≤n
  ≤-total zero (suc y) = inj₁ z≤n
  ≤-total (suc x) zero = inj₂ z≤n
  ≤-total (suc x) (suc y) with ≤-total x y
  ... | inj₁ x≤y = inj₁ (s≤s x≤y)
  ... | inj₂ y≤x = inj₂ (s≤s y≤x)
```

If I C-c C-n inside this hole I get the correct result!

```agda
  -- appendExample : Vector ℕ _≤_ 6 0
  -- appendExample = {! append {total = ≤-total} example1 example2 !}
```

One less obstacle in pursuit of our sorting function!

The next ingredient for the merge sort is the split function
which splits our vector in half.

The first problem we find here is that we have to specify the lower
bound for the second half of the vector we are splitting and this
bound needs to be exactly the element at index n ÷ 2. Another insight
is that split can be seen as simply using take and drop (if we ignore
the proof that the 2 halves appended have to be equal to the original).
`take` is straightforward to implement since the output vector preserves
the lower bound:

```agda
  take : ∀ {ℓ} {A} {_≾_} {n : ℕ} {b : A}
       → (m : ℕ)
       → Vector {ℓ} A _≾_ n b
       → Vector {ℓ} A _≾_ (m ⊓ n) b
  take zero _ = []
  take (suc _) [] = []
  take (suc m) ((a ∷ as) {p}) with take m as
  ... | res = (a ∷ res) {p-aux {m = m} p}
    where
      p-aux : ∀ {ℓ} {A} {_≾_} {n m : ℕ} {a b : A}
            → proof-≾ {ℓ} {_≾_ = _≾_} n a b
            → proof-≾ {ℓ} {_≾_ = _≾_} (m ⊓ n) a b
      p-aux {m = zero} p = tt
      p-aux {n = zero} {m = suc m} p = tt
      p-aux {n = suc n} {m = suc m} p = p
```

However `drop` is not as easy because we have to specify also that the
new lower bound should be the head of the resulting list if non-empty.

```agda
--  drop : ∀ {ℓ} {A} {_≾_} {n : ℕ} {b : A}
--       → (m : ℕ)
--       → Vector {ℓ} A _≾_ n b
--       → Vector {ℓ} A _≾_ (m ⊓ n) {!!}
--  drop m v = {!!}
```

This means that algorithms like mergesort or quicksort, that need to split the
array in half, require invariants that are not very easily or naturally expressable
on our refined vector data type. So, maybe this is a hint that we should pick a different
algorithm, but which one? After some thinking I think insertion sort might be the most natural.

There's only one important part for insertion sort and that is the `insert` function: 

```agda
  insert : ∀ {ℓ} {A} {_≾_} {n} {total : Total _≾_} {b}
         → (a : A)
         → Vector {ℓ} A _≾_ n b
         → Vector {ℓ} A _≾_ (1 + n) (min {total = total} a b)
  insert {total = total} {b = b} a v@[] with total a b
  ... | inj₁ a≾b = a ∷ v
  ... | inj₂ b≾a = b ∷ v
  insert {n = suc zero} {total = total} a ((b ∷ v@[]) {pb}) with total a b
  ... | inj₁ a≾b = (a ∷ (b ∷ v)) {a≾b}
  ... | inj₂ b≾a = (b ∷ (a ∷ v)) {b≾a}
  insert {n = suc (suc n)} {total = total} a ((b ∷ v) {pb}) with total a b
  ... | inj₁ a≾b = (a ∷ (b ∷ v) {pb}) {a≾b}
  ... | inj₂ b≾a = (b ∷ insert {total = total} a v) {p-aux {total = total} {n = n} b≾a pb}
     where
       p-aux : ∀ {ℓ} {A : Set ℓ} {_≾_} {total : Total _≾_} {n : ℕ} {a b lb : A}
             → a ≾ lb
             → a ≾ b
             → a ≾ min {total = total} lb b
       p-aux {total = total} {b = b} {lb = lb} a≾lb a≾b with total lb b
       ... | inj₁ _ = a≾lb
       ... | inj₂ _ = a≾b
```

This function requires `_≾_` to be a Total order and we can see it being needed to branch on different
cases and to prove our auxiliar lemma that allow us to massage our invariants into the correct type.

All that it's left is to write insertion sort which basically calls `insert` recursively for all elements
in a given vector:

```agda
  minimumBy : ∀ {ℓ} {A} {_≼_ _≾_ : Rel A ℓ} {n} {a}
            → Total _≾_
            → Vector {ℓ} A _≼_ (1 + n) a
            → A
  minimumBy total (a ∷ []) = a
  minimumBy {n = suc n} total (a ∷ v) = min {total = total} a (minimumBy total v)

  insertionSort : ∀ {ℓ} {A} {_≼_ _≾_ : Rel A ℓ} {n} {total : Total _≾_} {a}
                → (v : Vector {ℓ} A _≼_ (suc n) a)
                → Vector {ℓ} A _≾_ (suc n) (minimumBy total v)
  insertionSort {n = zero} {total = total} (a ∷ ([] {lb = lb})) = a ∷ ([] {lb = lb})
  insertionSort {n = suc n} {total = total} (a ∷ vv@(_ ∷ _)) = insert {total = total} a (insertionSort {total = total} vv)
```

Insertion sort requires that the lowerbound be the minimum value of the input vector according to a particular order.
We require that by building the `minimumBy` function and plug it into the the return vector type of the `insertionSort`
function. Yay dependent types!

After doing that the function is rather straightforward to write, requiring only pattern match on the vector so it can
know which branch from `minimumBy` to use. There's a slight limitation to the way I ended up doing things which is
the vector needs to be non-empty, since we can not compute the minimum value of an empty vector. This could be fixed by
requiring something like a lattice with a bottom value smaller than all other values of a particular Set. I am curious
to see if using open lower bound would relax this requirement too.

It looks like our hunch about changing sorting algorithms turned out to be true, and in hindsight I believe the reason to
be our data type is not able to elegantly capture the required invariants of divide-and-conquer algorithms, at least while trying
to be relation and data polymorphic.

All that's left is to give this a try with our example vectors:


```agda
  ≥-total : Total _≥_
  ≥-total zero zero = inj₁ z≤n
  ≥-total zero (suc y) = inj₂ z≤n
  ≥-total (suc n) zero = inj₁ z≤n
  ≥-total (suc x) (suc y) with ≥-total x y
  ... | inj₁ x≥y = inj₁ (s≤s x≥y)
  ... | inj₂ y≥x = inj₂ (s≤s y≥x)

  example3 : Vector ℕ _≥_ 3 5
  example3 = (5 ∷ (3 ∷ (0 ∷ [] {lb = zero})) {z≤n}) {s≤s (s≤s (s≤s z≤n))}

  example4 : Vector ℕ _≥_ 3 6
  example4 = (6 ∷ (4 ∷ (1 ∷ [] {lb = zero})) {s≤s z≤n}) {s≤s (s≤s (s≤s (s≤s z≤n)))}

  sortedExample : Vector ℕ _≤_ 6 0
  sortedExample = {! insertionSort {total = ≤-total} (append {total = ≥-total} example3 example4)!}
```
