Style guide for the standard library
====================================

This is very much a work-in-progress and is not exhaustive. Furthermore, many of
these are aspirations, and may be violated in certain parts of the library.
It is hoped that at some point a linter will be developed for Agda which will
automate most of this.

## File structure

* The standard library uses a standard line length of 72 characters. Please
  try to stay within this limit. Having said that this is the most violated
  rule in the style-guide and it is recognised that it is not always possible
  to achieve whilst using meaningful names.

#### Indentation

* The contents of a top-level module should have zero indentation.

* Every subsequent nested scope should then be indented by an additional
  two spaces.

* `where` blocks should be indented by two spaces and their contents
  should be aligned with the `where`.

* If the type of a term does not fit on one line then the subsequent
  lines of the type should all be aligned with the first character
  of the first line of type, e.g.
  ```agda
  map-cong₂ : ∀ {a b} {A : Set a} {B : Set b} →
              ∀ {f g : A → B} {xs} →
              All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
  ```

* As can be seen in the example above, function arrows at line breaks
  should always go at the end of the line rather than the beginning of the
  next line.

#### Empty lines

* All module headers and standard term definitions should have a single
  empty line after them.

* There should be _two_ empty lines between adjacent record or module definitions
  in order to better distinguish the end of the record or module, as they will
  already be using single empty lines between internal definitions.

* For example:
  ```agda
  module Test1 where

    def1 : ...
    def1 = ...

    def2 : ...
    def2 = ...


  module Test2 where

    record Record1 : Set where
      field
        field1 : ...

      aux1 : ...
      aux1 = ...

      aux2 : ...
      aux2 = ...


   record Record2 : Set where
     field
       field2 : ...


   record1 : Record1
   record1 = { field1 = ... }

   record2 : Record2
   record2 = { field2 = ... }
  ```

#### Modules

* As a rule of thumb, there should only be one named module per file. Anonymous
  modules are fine, but named internal modules should either be opened publicly
  immediately or split out into a separate file.

* Module parameters should be put on a single line if they fit.

* Otherwise, they should be spread out over multiple lines, each indented by two
  spaces. If they can be grouped logically by line, then it is fine to do so.
  Otherwise, a line each is probably clearest. The `where` keyword should be placed
  on an additional line of code at the end. For example:
  ```agda
  module Relation.Binary.Reasoning.Base.Single
    {a ℓ} {A : Set a} (_∼_ : Rel A ℓ)
    (refl : Reflexive _∼_) (trans : Transitive _∼_)
    where
  ```

* There should always be a single blank line after a module declaration.

#### Imports

* All imports should be placed in a list at the top of the file
  immediately after the module declaration.

* The list of imports should be declared in alphabetical order.

* If the module takes parameters that require imports from other files,
  then those imports only may be placed above the module declaration, e.g.
  ```agda
  open import Algebra using (Ring)

  module Algebra.Properties.Ring {a l} (ring : Ring a l) where

        ... other imports
  ```

* If it is important that certain names only come into scope later in
  the file then the module should still be imported at the top of the
  file but it can be imported *qualified*, i.e. given a shorter name
  using the keyword `as` and then opened later on in the file when needed,
  e.g.
  ```agda
  import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
  ...
  ...
  open SetoidEquality S
  ```

* If importing a parameterised module, qualified or otherwise, with its
  parameters instantiated, then such 'instantiated imports' should be placed
  *after* the main block of `import`s, and *before* any `variable` declarations.

* Naming conventions for qualified `import`s: if importing a module under
  a root of the form `Data.X` (e.g. the `Base` module for basic operations,
  or `Properties` for lemmas about them etc.) then conventionally, the
  qualified name(s) for the import(s) should (all) share as qualified name
  that of the name of the `X` datatype defined: i.e. `Data.Nat.Base`
  should be imported as `ℕ`, `Data.List.Properties` as `List`,  etc.
  In this spirit, the convention applies also to (the datatype defined by)
  `Relation.Binary.PropositionalEquality.*` which should be imported qualified
  with the name `≡`.
  Other modules should be given a 'suitable' qualified name based on its 'long'
  path-derived name (such as `SetoidEquality` in the example above); commonly
  occurring examples such as `Algebra.Structures` should be imported qualified
  as `Structures` etc.
  NB. Historical legacy means that these conventions have not always been observed!

* Special case of the above for `*-Reasoning` (sub-)modules: by analogy with
  `Relation.Binary.PropositionalEquality.≡-Reasoning`, when importing qualified
  the `-Reasoning` (sub-)module associated with a given (canonical) choice of
  symbol (eg. `≲` for `Preorder` reasoning), use the qualified name
  `<symbol>-Reasoning`, ie. `≲-Reasoning` for the example given.

* Qualified `open import`s should, in general, avoid `renaming`
  identifiers, in favour of using the long(er) qualified name,
  although similar remarks about legacy failure to observe this
  recommendation apply!
  NB. `renaming` directives are, of course, permitted when a module is
  imported qualified, in order to be *subsequently* `open`ed for
  `public` export (see below).

* When using only a few items (i.e. < 5) from a module, it is a good practice to
  enumerate the items that will be used by declaring the import statement
  with the directive `using`. This makes the dependencies clearer, e.g.
  ```agda
  open import Data.Nat.Properties using (+-assoc)
  ```

* Re-exporting terms from a module using the `public` modifier
  should *not* be done in the list of imports as it is very hard to spot.
  Instead, the best approach is often to rename the import and then open it
  publicly later in the file in a more obvious fashion, e.g.
  ```agda
  -- Import list
  ...
  import Data.Nat.Properties as NatProperties
  ...

  -- Re-export ring
  open NatProperties public
    using (+-*-ring)
  ```

* If multiple import modifiers are used, then they should occur in the
  following order: `public`, `using` `renaming`, and if `public` is used
  then the `using` and `renaming` modifiers should occur on a separate line.
  For example:
  ```agda
  open Monoid monoid public
    using (ε) renaming (_∙_ to _+_)
  ```

#### Layout of data declarations

* The `:` for each constructor should be aligned.

#### Layout of record declarations

* The `:` for each field should be aligned.

* If defining multiple records back-to-back then there should be a double
  empty line between each record.

#### Layout of record instances

* The `record` keyword should go on the same line as the rest of the proof.

* The next line with the first record item should start with a single `{`.

* Every subsequent item of the record should go on its own line starting with
  a `;`.

* The final line should end with `}` on its own.

* The `=` signs for each field should be aligned.

* For example:
  ```agda
  ≤-isPreorder : IsPreorder _≡_ _≤_
  ≤-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = ≤-reflexive
    ; trans         = ≤-trans
    }
  ```

#### Layout of initial `private` block

* Since the introduction of generalizable `variable`s (see below),
  this block provides a very useful way to 'fix'/standardise notation
  for the rest of the module, as well as introducing local
  instantiations of parameterised `module` definitions, again for the
  sake of fixing notation via qualified names.

* It should typically follow the `import` and `open` declarations, as
  above, separated by one blankline, and be followed by *two* blank
  lines ahead of the main module body.

* The current preferred layout is to use successive indentation by two spaces, eg.
  ```agda
  private
    variable
      a : Level
      A : Set a
  ```
  rather than to use the more permissive 'stacked' style, available
  since [agda/agda#5319](https://github.com/agda/agda/pull/5319).

* A possible exception to the above rule is when a *single* declaration
  is made, such as eg.
  ```agda
  private open module M = ...
  ```

#### Layout of `where` blocks

* `where` blocks are preferred rather than the `let` construction.

* The `where` keyword should be placed on the line below the main proof,
  indented by two spaces.

* If the content of the block is non-trivial then types should be
  provided alongside the terms, and all terms should be on lines after
  the `where`, e.g.
  ```agda
  statement : Statement
  statement = proof
    where
    proof : Proof
    proof = some-very-long-proof
  ```

* If the content of the block is trivial or is an `open` statement then
  it can be provided on the same line as the `where` and a type can be
  omitted, e.g.
  ```agda
  statement : Statement
  statement = proof
    where proof = x
  ```

#### Layout of equational reasoning

* The `begin` clause should go on the same line as the rest of the proof.

* Every subsequent combinator `_≡⟨_⟩_` should be placed on an additional
line of code, indented by two spaces.

* The relation sign (e.g. `≡`) for each line should be aligned if possible.

* For example:
  ```agda
  +-comm : Commutative _+_
  +-comm zero    n = sym (+-identityʳ n)
  +-comm (suc m) n = begin
    suc m + n    ≡⟨⟩
    suc (m + n)  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)  ≡⟨ sym (+-suc n m) ⟩
    n + suc m    ∎
  ```

* When multiple reasoning frameworks need to be used in the same file, the
  `open` statement should always come in a where clause local to the
  definition. This way users can easily see which reasoning toolkit is
  being used. For instance:
  ```agda
  foo m n p = begin
    (...) ∎
    where open ≤-Reasoning
  ```

#### Layout of deprecation blocks

* There is standard boilerplate text which should go at the end of a
  file, separated by two blank lines from the main module body:
  ```agda
------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.
  ```

* For each (new) version with deprecations, there should be a single
  line comment, separated by one blank line from the preceding
  deprecation block:
  ```agda
-- Version X.Y
  ```

* There is standard boilerplate text for deprecating `old-name` in
  favour of a definition in terms of `new-name`: the actual definition
  (which need not have a type signature if this is a simple matter of
  aliasing, or simple function composition), followed by:
  ```agda
{-# WARNING_ON_USAGE <old-name>
"Warning: <old-name> was deprecated in vX.Y.
Please use <newname> instead."
#-}
  ```
  where the advice on what to use instead may also contain additional
  information regarding eg. location, or usage patterns.

* Each entry in the block should be correlated with a suitable
  `CHANGELOG` entry for the associated release version.

#### Mutual and private blocks

* Non-trivial proofs in `private` blocks are generally discouraged. If it is
  non-trivial, then chances are that someone will want to reuse it at some
  point!

* Instead, private blocks should only be used to prevent temporary terms and
  records that are defined for convenience from being exported by the module.

* The mutual block is considered obsolete. Please use the standard approach
  of placing the type signatures of the mutually recursive functions before
  their definitions.

#### Function arguments

* Function arguments should be aligned between cases where possible, e.g.
  ```agda
  +-comm : Commutative _+_
  +-comm zero    n = ...
  +-comm (suc m) n = ...
  ```

* If an argument is unused in a case, it may at the author's
  discretion be replaced by an underscore, e.g.
  ```agda
  +-assoc : Associative _+_
  +-assoc zero    _ _ = refl
  +-assoc (suc m) n o = cong suc (+-assoc m n o)
  ```

* If it is necessary to refer to an implicit argument in one case then
  the implicit argument brackets must be included in every other case as
  well, e.g.
  ```agda
  m≤n⇒m∸n≡0 : ∀ {m n} → m ≤ n → m ∸ n ≡ 0
  m≤n⇒m∸n≡0 {n = n} z≤n       = 0∸n≡0 n
  m≤n⇒m∸n≡0 {n = _} (s≤s m≤n) = m≤n⇒m∸n≡0 m≤n
  ```

* As of Agda 2.6.0 dot patterns are no longer necessary when unifying
  function arguments and therefore should not be prepended to function
  arguments.

#### Comments

* Comments should be placed above a term rather than on the same line, e.g.
  ```agda
  -- Multiplication of two elements
  _*_ : A → A → A
  _*_ = ...
  ```
  rather than:
  ```agda
  _*_ : A → A → A -- Multiplication of two elements
  _*_ = ...
  ```

* Files can be separated into different logical parts using comments of
  the following style, where the header is 72 characters wide:
  ```agda
  ------------------------------------------------------------------------
  -- <Title>
  ```
  Use sentence case in the title: `Rounding functions`, not `Rounding Functions` or `ROUNDING FUNCTIONS`.

#### Other

* The `with` syntax is preferred over the use of `case` from the `Function`
  module. The `|` should not be aligned with the `with` statement, i.e.
  ```agda
  filter p (x ∷ xs) with p x
  ... | true  = x ∷ filter p xs
  ... | false = filter p xs
  ```
  instead of
  ```agda
  filter p (x ∷ xs) with p x
  ...                  | true  = x ∷ filter p xs
  ...                  | false = filter p xs
  ```

* Instance arguments, and their types, should use the vanilla ASCII/UTF-8 `{{_}}`
  syntax in preference to the Unicode `⦃_⦄` syntax (written using `\{{`/`\}}`),
  which moreover requires additional whitespace to parse correctly.
  NB. Even for irrelevant instances, such as typically for `NonZero` arguments,
  nevertheless it is necessary to supply an underscore binding `{{_ : NonZero n}}`
  if subsequent terms occurring in the type rely on that argument to be well-formed:
  eg in `Data.Nat.DivMod`, in the use of `_/ n` and `_% n`
  ```agda
  m≡m%n+[m/n]*n : ∀ m n .{{_ : NonZero n}} → m ≡ m % n + (m / n) * n
  ```

## Types

#### Implicit and explicit arguments

* Function arguments should be implicit if they can "almost always"
  be inferred. If there are common cases where they cannot be inferred
  then they should be left explicit.

* If there are lots of implicit arguments that are common to a collection
  of proofs they should be extracted by using an anonymous module.

#### Variables

* `Level` and `Set`s can always be generalised using the keyword `variable`.

* A file may only declare variables of other types if those types are used
  in the definition of the main type that the file concerns itself with.
  At the moment the policy is *not* to generalise over any other types to
  minimise the amount of information that users have to keep in their head
  concurrently.

* Example 1: the main type in `Data.List.Properties` is `List A` where `A : Set a`.
  Therefore it may declare variables over `Level`, `Set a`, `A`, `List A`. It may
  not declare variables, for example, over predicates (e.g. `P : Pred A p`) as
  predicates are not used in the definition of `List`, even though they are used
  in many list functions such as `filter`.

* Example 2: the main type in `Data.List.Relation.Unary.All` is `All P xs` where
  `A : Set a`, `P : Pred A p`, `xs : List A`. It therefore may declare variables
  over `Level`, `Set a`, `A`, `List A`, `Pred A p`. It may not declare, for example,
  variables of type `Rel` or `Vec`.

## Naming conventions

* Names should be descriptive - i.e. given the name of a proof and the
  module it lives in, then users should be able to make a reasonable
  guess at its meaning.

* Terms from other modules should only be renamed to avoid name clashes,
  otherwise, all names should be used as defined.

* Datatype names should be capitalized, being its first letter in uppercase
and the remaining letters in lowercase.

* Function names should follow the camelCase naming convention, in which each
word within a compound word is capitalized except for the first word.

#### Variables

* Sets are named `A`, `B`, `C` etc.

* Predicates are named `P`, `Q`, `R` etc.

* Relations are named either `R`, `S`, `T` in the general case
  or `_≈_`/`_∼_`/`_≤_`/`_<_` if they are known to be an
  equivalence/preorder/partial order/strict partial order.

* Level variables are typically chosen to match the name of the
  relation, e.g. `a` for the level of a set `A`, `p` for a predicate
  `P`. By convention the name `0ℓ` is preferred over `zero` for the
  zeroth level.

* Natural variables are named `m`, `n`, `o`, ... (default `n`)

* Integer variables are named `i`, `j`, `k`, ... (default `i`)

* Rational variables are named `p`, `q`, `r`, ... (default `p`)

* All other variables should be named `x`, `y`, `z`.

* Collections of elements are usually indicated by appending an `s`
  (e.g. if you are naming your variables `x` and `y` then lists
  should be named `xs` and `ys`).

#### Preconditions and postconditions

* Preconditions should only be included in names of results if
  "important" (mostly a judgment call).

* Preconditions of results should be prepended to a description
  of the result by using the symbol `⇒` in names (e.g. `asym⇒antisym`)

* Preconditions and postconditions should be combined using the symbols
  `∨` and `∧` (e.g. `m*n≡0⇒m≡0∨n≡0`)

* Try to avoid the need for bracketing, but if necessary, use square
  brackets (e.g. `[m∸n]⊓[n∸m]≡0`)

* When naming proofs, the variables should occur in alphabetical order,
  e.g. `m≤n+m` rather than `n≤m+n`.

#### Operators and relations

* Concrete operators and relations should be defined using
  [mixfix](https://agda.readthedocs.io/en/latest/language/mixfix-operators.html)
  notation where applicable (e.g. `_+_`, `_<_`)

* Common properties such as those in rings/orders/equivalences etc.
  have defined abbreviations (e.g. commutativity is shortened to `comm`).
  `Data.Nat.Properties` is a good place to look for examples.

* Properties should be prefixed by the relevant operator/relation and
  separated from its name by a hyphen `-` (e.g. commutativity of sum
  results in a compositional name `+-comm` where `-` acts as a separator).

* If the relevant Unicode characters are available, negated forms of
  relations should be used over the `¬` symbol (e.g. `m+n≮n` should be
  used instead of `¬m+n<n`).

#### Symbols for operators and relations

* The stdlib aims to use a consistent set of notations, governed by a
  consistent set of conventions, but sometimes, different
  Unicode/emacs-input-method symbols nevertheless can be rendered by
  identical-*seeming* symbols, so this is an attempt to document these.

* The typical binary operator in the `Algebra` hierarchy, inheriting
  from the root `Structure`/`Bundle` `isMagma`/`Magma`, is written as
  infix `∙`, obtained as `\.`, NOT as `\bu2`. Nevertheless, there is
  also a 'generic' operator, written as infix `·`, obtained as
  `\cdot`. Do NOT attempt to use related, but typographically
  indistinguishable, symbols.

* Similarly, 'primed' names and symbols, used to standardise names
  apart, or to provide (more) simply-typed versions of
  dependently-typed operations, should be written using `\'`, NOT the
  unmarked `'` character.

* Likewise, standard infix symbols for eg, divisibility on numeric
  datatypes/algebraic structure, should be written `\|`, NOT the
  unmarked `|` character. Ditto. mutual divisibility `\||` etc. An
  exception to this is the *strict* ordering relation, written using
  `<`, NOT `\<` as might be expected.

* Since v2.0, the `Algebra` hierarchy systematically introduces
  consistent symbolic notation for the negated versions of the usual
  binary predicates for equality, ordering etc. These are obtained
  from the corresponding input sequence by adding `n` to the symbol
  name, so that `≤`, obtained as `\le`, becomes `≰` obtained as
  `\len`, etc.

* Correspondingly, the flipped symbols (and their negations) for the
  converse relations are systematically introduced, eg `≥` as `\ge`
  and `≱` as `\gen`.

* Any exceptions to these conventions should be flagged on the GitHub
  `agda-stdlib` issue tracker in the usual way.

#### Fixity

All functions and operators that are not purely prefix (typically
anything that has a `_` in its name) should have an explicit fixity
declared for it. The guidelines for these are as follows:

General operations and relations:

* binary relations of all kinds are `infix 4`

* unary prefix relations `infix 4 ε∣_`

* unary postfix relations `infixr 8 _∣0`

* multiplication-like: `infixl 7 _*_`

* addition-like  `infixl 6 _+_`

* arithmetic prefix minus-like  `infix  8 -_`

* arithmetic infix binary minus-like `infixl 6 _-_`

* and-like  `infixr 7 _∧_`

* or-like  `infixr 6 _∨_`

* negation-like `infix 3 ¬_`

* post-fix inverse  `infix  8 _⁻¹`

* bind `infixl 1 _>>=_`

* list concat-like `infixr 5 _∷_`

* ternary reasoning `infix 1 _⊢_≈_`

* composition `infixr 9 _∘_`

* application `infixr -1 _$_ _$!_`

* combinatorics `infixl 6.5 _P_ _P′_ _C_ _C′_`

* pair `infixr 4 _,_`

Reasoning:

* QED  `infix  3 _∎`

* stepping  `infixr 2 _≡⟨⟩_ step-≡ step-≡˘`

* begin  `infix  1 begin_`

Type formers:

* product-like `infixr 2 _×_ _-×-_ _-,-_`

* sum-like `infixr 1 _⊎_`

* binary properties `infix 4 _Absorbs_`

#### Functions and relations over specific datatypes

* When defining a new relation `P` over a datatype `X` in a `Data.X.Relation` module,
  it is often common to define how to introduce and eliminate that relation
  with respect to various functions. Suppose you have a function `f`, then
  - `f⁺` is a lemma of the form `Precondition -> P(f)`
  - `f⁻` is a lemma of the form `P(f) -> Postcondition`
  The logic behind the name is that `⁺` makes f appear in the conclusion while
  `⁻` makes it disappear from the hypothesis.

  For example, in `Data.List.Relation.Binary.Pointwise` we have `map⁺` to show
  how the `map` function may be introduced and `map⁻` to show how it may be
  eliminated:
  ```agda
  map⁺ : Pointwise (λ a b → R (f a) (g b)) as bs → Pointwise R (map f as) (map g bs)
  map⁻ : Pointwise R (map f as) (map g bs) → Pointwise (λ a b → R (f a) (g b)) as bs
  ```

* When specifying a property over a container, there are usually two choices. Either
  assume the property holds for generally (e.g. `map id xs ≡ xs`) or a assume that
  it only holds for the elements within the container (e.g. `All (λ x → f x ≡ x) xs → map f xs ≡ xs`).
  The naming convention is to add a `-local` suffix on to the name of the latter variety.
  e.g.
  ```agda
  map-id       :  map id xs ≡ xs
  map-id-local :  All (λ x → f x ≡ x) xs → map f xs ≡ xs
  ```

#### Keywords

* If the name of something clashes with a keyword in Agda, then convention
  is to place angular brackets around the name, e.g. `⟨set⟩` and `⟨module⟩`.

#### Reflected syntax

* When using reflection, the name of anything of type `Term` should be preceded
  by a backtick. For example ```List : Term → Term`` would be the function
  constructing the reflection of the `List` type.

* The names of patterns for reflected syntax are also *appended* with an
  additional backtick.

#### Specific pragmatics/idiomatic patterns

## Use of `pattern` synonyms

In general, these are intended to be used to provide specialised
constructors for `Data` types (and sometimes, inductive
families/binary relations such as `Data.Nat.Divisibility._∣_`), and as
such, their use should be restricted to `Base` or `Core` modules, and
not pollute the namespaces of `Properties` or other modules.

## Use of `with` notation

Thinking on this has changed since the early days of the library, with
a desire to avoid 'unnecessary' uses of `with`: see Issues
[#1937](https://github.com/agda/agda-stdlib/issues/1937) and
[#2123](https://github.com/agda/agda-stdlib/issues/2123).

## Proving instances of `Decidable` for sets, predicates, relations, ...

Issue [#803](https://github.com/agda/agda-stdlib/issues/803)
articulates a programming pattern for writing proofs of decidability,
used successfully in PR
[#799](https://github.com/agda/agda-stdlib/pull/799) and made
systematic for `Nary` relations in PR
[#811](https://github.com/agda/agda-stdlib/pull/811)

