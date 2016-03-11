# The DOT Calculus

A minimally complete version of dependent object types. The calculus comprises functions,
labeled types and terms combined through intersections, recursive bindings, and nothing else.

The [meta theory](#meta-theory) establishes type safety, a result that has also been fully mechanized.
Here is [the corresponding Coq script](dot_top_bot.v).

## Abstract Syntax

    Term member     a, b, c
    Type member     A, B, C
    Variable        x, y, z

    Type     S, T, U = {a: T}                       field declaration
                       {A: S..T}                    type declaration
                       S & T                        intersection
                       x.A                          projection
                       μ(x: T)                    recursive dependent type
                       ∀(x: S)T                     dependent function
                       Top                          top type
                       Bot                          bottom type

    Value          v = new(x: T)d                   object
                       λ(x: T)t                     lambda

    Term     s, t, u = x                            variable
                       v                            value
                       x.a                          selection
                       x y                          application
                       let x = t in u               let

    Definition     d = {a = t}                      field definition
                       {A = T}                      type definition
                       d & d'                       aggregate definition

    Store          s = ... x = v ...
    Environment    Γ = ... x: T ...

***

### Evaluation: `s | t -> s' | t'`

    (Project)
                             s | x.a  -->  s | t          if s(x) = new(x: T)(d, a = t)
    (Apply)
                             s | x y  -->  s | [z:=y]t    if s(x) = λ(z: T)t
    (Let-Var)
                  s | let x = y in t  -->  s | [x:=y]t
    (Let-Value)
                  s | let x = v in t  -->  s, x = v | t
    (Ctx)
                               s | t  -->  s' | t'
                      ------------------------------------
                      let x = t in u  -->  let x = t' in u

***

## Typing Rules

### Type Assignment `Γ ⊢ t: T`

    (Var)
                            Γ, x: T, Γ' ⊢ x: T
    (All-I)
                       Γ, x: T ⊢ t: U    (x ∉ fv(T))
                       -----------------------------------
                          Γ ⊢ λ(x: T)t: ∀(x: T)U
    (All-E)
                       Γ ⊢ x: ∀(z: S)T    Γ ⊢ y: S
                       -------------------------------
                              Γ ⊢ x y: [z:=y]T
    ({}-I)
                               Γ, x: T ⊢ d: T
                          --------------------------
                          Γ ⊢ new(x: T)d: μ(x: T)
    ({}-E)
                                Γ ⊢ x: {a: T}
                                --------------
                                 Γ ⊢ x.a: T
    (Let)
                Γ ⊢ t: T   Γ, x: T ⊢ u: U   (x ∉ fv(U))
                ----------------------------------------------
                            Γ ⊢ let x = t in u: U
    (Rec-I)
                                  Γ ⊢ x: T
                              -----------------
                              Γ ⊢ x: μ(x: T)
    (Rec-E)
                              Γ ⊢ x: μ(x: T)
                              -----------------
                                  Γ ⊢ x: T
    (&-I)
                            Γ ⊢ x: T   Γ ⊢ x: U
                            ---------------------
                                Γ ⊢ x: T & U
    (Sub)
                           Γ ⊢ t: T   Γ ⊢ T <: U
                           -----------------------
                                  Γ ⊢ t: U

***

### Definition Type Assignment `Γ ⊢ d: T`

    (Fld-I)
                                  Γ ⊢ t: T
                             --------------------
                             Γ ⊢ {a = t}: {a: T}
    (Typ-I)
                           Γ ⊢ {A = T}: {A: T..T}
    (AndDef-I)
           Γ ⊢ d<sub>1</sub>: T<sub>1</sub>   Γ ⊢ d<sub>2</sub>: T<sub>2</sub>   (dom(d<sub>1</sub>), dom(d<sub>2</sub>) disjoint)
           -------------------------------------------------------
                            Γ ⊢ d<sub>1</sub> & d<sub>2</sub>: T<sub>1</sub> & T<sub>2</sub>


***

### Subtyping: `Γ ⊢ T <: U`

    (<:-Top)
                                Γ ⊢ T <: Top
    (Bot-<:)
                                Γ ⊢ Bot <: T
    (Refl-<:)
                                Γ ⊢ T <: T
    (Trans-<:)
                          Γ ⊢ S <: T   Γ ⊢ T <: U
                          -------------------------
                                 Γ ⊢ S <: U
    (And-<:)
                               Γ ⊢ T & U <: T

                               Γ ⊢ T & U <: U
    (<:-And)
                          Γ ⊢ S <: T   Γ ⊢ S <: U
                          -------------------------
                                  S <: T & U
    (Fld-<:-Fld)
                                 Γ ⊢ T <: U
                            ---------------------
                            Γ ⊢ {a: T} <: {a: U}
    (Typ-<:-Typ)
                        Γ ⊢ S<sub>2</sub> <: S<sub>1</sub>   Γ ⊢ T<sub>1</sub> <: T<sub>2</sub>
                       -------------------------------
                       Γ ⊢ {A: S<sub>1</sub>..T<sub>1</sub>} <: {A: S<sub>2</sub>..T<sub>2</sub>}
    (<:-Sel)
                              Γ ⊢ x: {A: S..T}
                              -----------------
                                Γ ⊢ S <: x.A
    (Sel-<:)
                              Γ ⊢ x: {A: S..T}
                              -----------------
                               Γ ⊢ x.A <: T
    (All-<:-All)
                     Γ ⊢ S<sub>2</sub> <: S<sub>1</sub>   Γ, x: S<sub>2</sub> ⊢ T<sub>1</sub> <: T<sub>2</sub>
                     ------------------------------------
                      Γ ⊢ ∀(x: S<sub>1</sub>)T<sub>1</sub> <: ∀(x: S<sub>2</sub>)T<sub>2</sub>


*Note:* `Γ, x: T` is well-defined only if `x` is neither in the domain of `Γ` nor in
its free variables.

***

## Abbreviations

Group multiple intersected definitions or declarations in one pair of braces, replacing `&` with `;`. E.g.

             { A = T; a = t }  ===  { A = T } & { a = t }
            { A: S..T; a: T }  ===  { A: S..T } & { a: T }

Allow terms in applications and selections, using the expansions

                          t u  ===  let x = t in x u
                          x u  ===  let y = u in x y
                          t.a  ===  let x = t in x.a

Expand type ascriptions to applications:

                         t: T  ===  (λ(x: T)x)t

Shorthand syntax for object types and values:

         { z => D1; ...; Dn }  ===  μ(z: D1 & ... & Dn)
     new { z => d<sub>1</sub>; ...; dn }  ===  new(x: D1 & ... & Dn)d<sub>1</sub> & ... & dn
                                    where Di derived from di. (di needs to have full type info)

One can leave out the `z =>` if `z` does not appear in the rest of the term.

Shorthand syntax for self bounds: In type of `x`, expand

                      A <: T   ===  A: Bot .. T
                      A >: S   ===  A: S .. Top
                       A = T   ===  A: T .. T
                           A   ===  A: Bot .. Top

<!---
## Examples

    let scala_units =
      let scala_units_impl =
        new (su:
              { Unit: ∀(x: su.Unit)su.Unit..∀(x: su.Unit)su.Unit } &
              { unit: su.Unit }
            ) { Unit = ∀(x: su.Unit)su.Unit } &
              { unit = λ(x: su.Unit)x }
      in let scala_units_api_wrapper =
        λ(x:
          { a: μ(su:
                    { Unit: su.Unit..su.Unit } &
                    { unit: su.Unit }
                  )
          }
        )x
      in scala_units_api_wrapper scala_units_impl

Or, using some of the shorthands:

    let scala_units =
      new (su: {
        Unit: ∀(x: su.Unit)su.Unit .. ∀(x: su.Unit)su.Unit
        unit: su.Unit
      }) {
        Unit = ∀(x: su.Unit)su.Unit
        unit = λ(x: su.Unit)x
      }: { su =>
        Unit: su.Unit .. su.Unit
        unit: su.Unit
      }

Or, even shorter:

    let scala_units =
      new { su =>
        Unit = ∀(x: su.Unit)su.Unit
        unit: su.Unit = λ(x: su.Unit)x
      }: { su =>
        Unit
        unit: su.Unit
      }

Encoding a generic list type:

    let scala_collections_immutable =
      new { sci =>
        List = { thisList => A; head: thisList.A; tail: sci.List & { A = thisList.A } }
        nil: ∀(x: {A})sci.List & {A = x.A} =
          λ(x: {A})
            let thisList = new { thisList => A = x.A; head = thisList.head; tail = thisList.tail }
            in thisList
        cons: ∀(x: {A})∀(hd: x.A)∀(tl: sci.List & {A = x.A})sci.List & {A = x.A} =
          λ(x: {A})λ(hd: x.A)λ(tl: sci.List & {A = x.A})
             let thisList = new { thisList => A = x.A; head = hd; tail = tl }
             in thisList
      }: { sci =>
        List <: { thisList => A; head: thisList.A; tail: sci.List & { A = thisList.A } }
        nil: ∀(x: {A})sci.List & {A = x.A}
        cons: ∀(x: {A})∀(hd: x.A)∀(tl: sci.List & {A = x.A})sci.List & {A = x.A}
      }

Here's a detailed argument why the body of the `cons` method has the required type
`sci.List & { A = x.A }`:

(1) We have:

       thisList: μ(thisList: { A = x.A, hd: x.A, tl: sci.List & {A = x.A}})

            by (Rec-E)

       thisList: { A = x.A, hd: x.A, tl: sci.List & {A = x.A}}

             by (Sub), since thisList.A <: x.A

       thisList: { A = x.A, hd: thisList.A, tl: sci.List & {A = thisList.A}}

             by (Sub), since {A: x.A..x.A} <: {A: Bot..Top}

       thisList: { A, hd: thisList.A, tl: sci.List & { A = thisList.A}}

             by (Rec-I)

       thisList: μ(thisList: { A, hd: thisList.A, tl: sci.List & { A = thisList.A}})

             by (Sub), since
             μ(thisList: { A, hd: thisList.A, tl: sci.List & { A = thisList.A}})
               <: sci.List

       thisList: sci.List

(2) We also have:

     thisList: { A = x.A, hd: x.A, tl: sci.List & {A = x.A}}

        by (Sub)

     thisList: {A = x.A}

(1) and (2) together give with (&-I)

     thisList: sci.List & { A = x.A }


Generally, we can encode:

  - abstract types
  - dependent function types
  - type parameters
  - covariant parameterized types
  - algebraic data types
  - modules
  - functors
  - objects
  - classes
-->

## Meta Theory

### Definition (Precise typing)

`Γ ⊢! t: T` if `Γ ⊢ t: T` and the following two conditions hold:

 1. If `t` is a value, the typing derivation of `t` ends in (All-I) or ({}-I).
 2. If `t` is a variable, the typing derivation of `t` consists only of (Var), (Rec-E)
    and (Sub) steps and every (Sub) step makes use of only the subtyping rules (And-<:)
    and (Trans).

### Definition (Environment/store correspondence)

An environment `Γ` corresponds to a store `s`, written `Γ ~ s`, if `Γ ~ s` can be derived
using the rules below.

                              (empty) ~ (empty)

                              Γ ~ s   Γ ⊢! v: T
                              ------------------
                              Γ, x: T ~ s, x = v

### Definition (Underlying value)
Given a store `s` and a variable `x` bound in `s`,
the underlying value `s(x)` is the value `v` such that `x = v in s`.

### Lemma (Weakening)
Let `Γ = Γ', x: S`. Then

 - If `Γ' ⊢ t: T` then `Γ ⊢ t: T`
 - If `Γ' ⊢! v: T` then `Γ ⊢! v: T`.
 - If `Γ' ⊢ T <: U` then `Γ ⊢ T <: U`.
 - If `Γ' ~ s` then `Γ ~ s`.

*Proof*: All derivations remain valid in an environment with extra information.

### Definition (Environment subsumption)

Environment `Γ` subsumes `Γ'`, written `Γ <: Γ'`, if
for all `x: T` in `Γ'` we have `Γ ⊢ x: T`.


### Lemma (Narrowing)

If `Γ <: Γ'` then:

 - If `Γ' ⊢ t: T` then also `Γ ⊢ t: T`
 - If `Γ' ⊢ d: T` then also `Γ ⊢ d: T`
 - If `Γ' ⊢ S <: T` then also `Γ' ⊢ S <: T`

*Proof*: A straightforward induction on typing, subtyping and well-formedness derivations.


### Definition (Environment Renaming)

    [x:=y]Γ = [[x:=y]z: [x:=y]T | z: T in Γ]

### Lemma (Renaming)
Let [s] be a renaming `[x<sub>0</sub>:=y<sub>0</sub>]` for arbitrary variables `x<sub>0</sub>`, `y<sub>0</sub>`. Then

 - `     [s]μ(x: T)  =  μ([s]x: [s]T)`
 - `    [s]∀(x: T)U  =  ∀([s]x: [s]T): [s]U`
 - `    [s]new(x: T)d  =  new([s]x: [s]T): [s]d`
 - ` [s]λ(x: T)t  =  λ([s]x: [s]T): [s]t`
 - `[s]let x = t in u  =  let [s]x = [s]t in [s]u`

*Proof*. We prove the first equation; the others are analogous. We distinguish whether or not `x<sub>0</sub> = x`.

If `x<sub>0</sub> = x` then

      [s]μ(x<sub>0</sub>: T)
    = (by definition of substitution)
      μ(x<sub>0</sub>: T)
    = (by alpha renaming x<sub>0</sub> to y<sub>0</sub>)
      μ(y<sub>0</sub>: [y<sub>0</sub>:=x<sub>0</sub>]T)
    = (by rewriting)
      μ([s]x<sub>0</sub>: [s]T)

If `x<sub>0</sub> != x` then

      [s]μ(x: T)
    = (by definition of substitution)
      μ(x: [s]T)
    = (since x<sub>0</sub> != x)
      μ([s]x<sub>0</sub>: [s]T)

### Lemma (Subst)
 1. If `Γ, x: S ⊢ t: T` and `Γ ⊢ y: [x:=y]S`
then `Γ ⊢ [x:=y]t: [x:=y]T`.
 2. If `Γ, x: S ⊢ d: T` and `Γ ⊢ y: [x:=y]S`
then `Γ ⊢ [x:=y]d: [x:=y]T`.

We prove the more general proposition:

If `Γ, x: S, Γ' ⊢ t: T` and `Γ, [x:=y]Γ' ⊢ y: [x:=y]S`, then
`Γ, [x:=y]Γ' ⊢ [x:=y]t: [x:=y]T`. (and the same for `d` instead of `t`).

Proof by mutual induction on derivations.
Let `[s] = [x<sub>0</sub>:=y<sub>0</sub>]`.
Assume `Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ t<sub>0</sub>: T<sub>0</sub>` and `Γ, [s]Γ' ⊢ y<sub>0</sub>: [s]S<sub>0</sub>`.
To show: `Γ, [s]Γ' ⊢ [s]t<sub>0</sub>: [s]T<sub>0</sub>`.

We distinguish according to the last rule in the derivation of `Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ t<sub>0</sub>: T<sub>0</sub>`

**Case (Var)**: We have in this case: `t = x<sub>0</sub>`, `T<sub>0</sub> = S<sub>0</sub>`,
`Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ x: S<sub>0</sub>`, and `Γ, [s]Γ' ⊢ y<sub>0</sub>: [s]S<sub>0</sub>`.
Together, `Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ [s]x<sub>0</sub>: [s]S<sub>0</sub>`.

**Case (All-I)** Then `t<sub>0</sub> = λ(x: T)t` and the last rule is

                     Γ, x<sub>0</sub>: S<sub>0</sub>, Γ', x: T ⊢ t: U
              ------------------------------------------
              Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ λ(x: T)t: ∀(x: T)U

By the I.H., `Γ, [s]Γ', [s]x: [s]T ⊢ [s]t: [s]U`.
By (All-I), `Γ, [s]Γ' ⊢ λ([s]x: [s]T)[s]t): ∀([s]x: [s]T)[s]U`.
By applying Lemma (Renaming) twice to the RHS, `Γ, [s]Γ' ⊢ [s]λ(x: T)t): [s]∀(x: T)U`.

**Case (All-E)** Then `t<sub>0</sub> = x y` and the last rule is

       Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ x: ∀(y: S)T    Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ y: S
       -------------------------------------------------------
                    Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ x y: [z:=y]T

By the. I.H., `Γ, [s]Γ' ⊢ [s]x: ∀(z: [s]S)[s]T` and `Γ, [s]Γ' ⊢ [s]y: [s]S`.
By (All-E), `Γ, [s]Γ' ⊢ [s]x [s]y: [z:=[s]y][s]T`.
W.l.o.g choose `z` so that `z != x<sub>0</sub>`, `z != y`.
Hence, `[z:=[s]z][s]` = [s][z:=y]. Together,
`Γ,[s]Γ' ⊢ [s](x y): [s][z:=y]T`.

**Case ({}-I)**: Then `t<sub>0</sub> = new(x: T)d` and the last rule is

                     Γ, x<sub>0</sub>: S<sub>0</sub>, Γ', x: T ⊢ d: T
                --------------------------------------
                Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ new(x: T)d: μ(x: T)

By the I.H., `Γ, [s]Γ', [s]x: [s]T ⊢ [s]d: [s]T`.
By ({}-I), `Γ, [s]Γ' ⊢ new([s]x: [s]T)[s]d: μ([s]x: [s]T)`
By applying Lemma (Renaming) twice to the RHS,
`Γ, [s]Γ' ⊢ [s]new(x: T)d: [s]μ(x: T)`.

**Case ({}-E)** Then `t<sub>0</sub> = x.a` and the last rule is:

                     Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ x: {a: T}
                     ---------------------------
                       Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ x.a: T

By the I.H., `Γ, [s]Γ' ⊢ [s]x: {a: [s]T}`.
By ({}-E), `Γ, [s]Γ' ⊢ [s]x.a: [s]T`.

**Case (Let)**: Then `t<sub>0</sub> = let x = t in u` and the last rule is:

    Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ t: T   Γ, x<sub>0</sub>: S<sub>0</sub>, Γ', x: T ⊢ u: U   (x ∉ fv(U))
    ----------------------------------------------------------------------
                      Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ let x = t in u: U

By the I.H., `Γ, [s]Γ' ⊢ [s]t: [s]T` and `Γ, [s]Γ', [s]x: [s]T ⊢ [s]u: [s]U`.
With (Let) it follows that `Γ, [s]Γ' ⊢ let [s]x = [s]t in [s]u: [s]U`.
By (Renaming), `Γ, [s]Γ' ⊢ [s]let x = t in u: [s]U`.

**Case (Rec-I)**: Then `t<sub>0</sub> = x` and the last rule is:

                              Γ ⊢ x: T
                          -----------------
                          Γ ⊢ x: μ(x: T)

By the I.H., `Γ, [s]Γ' ⊢ [s]x: [s]T`.
By (Rec-I), `Γ, [s]Γ' ⊢ [s]x: μ([s]x: [s]T)`.
By applying Lemma (Renaming) to the `rec` term, `Γ, [s]Γ' ⊢ [s]x: [s]μ(x: T)`.

**Case (Rec-E)**: Then `t<sub>0</sub> = x` and the last rule is:

                    Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ x: μ(x: T)
                    -----------------------------
                        Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ x: T

By the I.H., `Γ, [s]Γ' ⊢ [s]x: [s]μ(x: T)`.
By applying Lemma (Renaming) to the `rec` term, `Γ, [s]Γ' ⊢ [s]x: μ([s]x: [s]T)`.
By (Rec-E), `Γ, [s]Γ' ⊢ [s]x: [s]T`.

**Case (&=I)**. Then `t<sub>0</sub> = x` amd the last rule is:

                        Γ ⊢ x: T   Γ ⊢ x: U
                        ---------------------
                            Γ ⊢ x: T & U

By the I.H., `Γ, [s]Γ' ⊢ [s]x: [s]T` and `Γ, [s]Γ' ⊢ [s]x: [s]U`.
By (&=I), `Γ, [s]Γ' ⊢ [s]x: [s]T & [s]U`.

**Case (Sub)** Then `t<sub>0</sub> = t` and the last rule is:

           Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ t: T   Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ T <: U
           -----------------------------------------------
                        Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ t: U

By the I.H., `Γ, [s]Γ' ⊢ [s]t: [s]T`.
By (Subst-<:), `Γ, [s]Γ' ⊢ [s]T <: [s]U`.
By (Sub), `Γ, [s]Γ' ⊢ [s]T: [s]U`.

**Case (Fld)**. Then `t<sub>0</sub> = {a = t}` and the last rule is:

                        Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ t: S
                   --------------------------------
                   Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ {a = t}: {a: T}

By the I.H, `Γ, [s]Γ' ⊢ [s]t: [s]S`.
By (Fld), `Γ, [s]Γ' ⊢ {a = [s]t}: {a: [s]T}`.
Rewriting this gives `Γ, [s]Γ' ⊢ [s]{a = t}: [s]{a: T}`.

**Cases (Typ), (And)** are analogous to (Fld).

***


### Lemma (Subst-<:)

If `Γ, x: S, Γ' ⊢ T <: U` and
`Γ, [x:=y]Γ' ⊢ y: [x:=y]S`, then
`Γ, [x:=y]Γ' ⊢ [x:=y]T <: [x:=y]U`.

Proof by mutual induction on derivations.
Let [s] = [x<sub>0</sub>:=y<sub>0</sub>].
Assume `Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ T<sub>0</sub> <: U<sub>0</sub>` and `Γ, [s]Γ' ⊢ y<sub>0</sub>: [s]S<sub>0</sub>`.
To show: `Γ [s]Γ' ⊢ [s]T<sub>0</sub> <: [s]U<sub>0</sub>`.

We only show two cases; the others are similar.

**Case(<:-Sel)**: Then `T<sub>0</sub> = S` and the last rule of `D` is:

                    Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ x: {A: S..T}
                    -----------------------------
                      Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ S <: x.A

By the I.H., `Γ, [s]Γ' ⊢ [s]x: {A: [s]S..[s]T}`.
By (<:-Sel), `Γ, [s]Γ' ⊢ [s]S <: [s]x.A`.

**Case (All-<:-All)** Then `T<sub>0</sub> = ∀(x: S<sub>1</sub>)T<sub>1</sub>` and the last rule is:

     Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ S<sub>2</sub> <: S<sub>1</sub>   Γ, x<sub>0</sub>: S<sub>0</sub>, Γ', x: S<sub>2</sub> ⊢ T<sub>1</sub> <: T<sub>2</sub>
     ------------------------------------------------------------
            Γ, x<sub>0</sub>: S<sub>0</sub>, Γ' ⊢ ∀(x: S<sub>1</sub>)T<sub>1</sub> <: ∀(x: S<sub>2</sub>)T<sub>2</sub>

By the I.H., `Γ, [s]Γ' ⊢ [s]S<sub>2</sub> <: [s]S<sub>1</sub>` and
`Γ, [s]Γ', [s]x: [s]S<sub>2</sub> ⊢ [s]T<sub>1</sub> <: [s]T<sub>2</sub>`.
By (All-<:-All), `Γ, [s]Γ' ⊢ ∀([s]x: [s]S<sub>1</sub>)[s]T<sub>1</sub> <: ∀([s]x: [s]S<sub>1</sub>)[s]T<sub>1</sub>`.
By (Renaming), `Γ, [s]Γ' ⊢ [s]∀(x: S<sub>1</sub>)T<sub>1</sub> <: [s]∀(x: S<sub>2</sub>)T<sub>2</sub>`.


### Lemma (Corresponding Definition Types)

If `Γ ~ s` and `s(x) = new(x: S)d` for some definitions `d = d<sub>1</sub> & ... & dn` then
 1. `x: μ(x: S) in Γ`.
 2. `S = S<sub>1</sub> & ... & Sn` where for each `i` either

    - `di` is of the form `{a = t}` and `Si = {a: T}` for some `T` such that `Γ ⊢ t: T`, or
    - `di` is of the form `{A = T}` and `Si = {A: T..T}`.

*Proof* By the definition of `~`, `Γ` contains a binding for `x`, say
`Γ = G1,x:T,G2` such that `G1 ⊢ s(x): T`. Also by the definition of `~` and with ({}-I),
`G1 ⊢! new(x: S)d: μ(x: S)`, which establishes (1).
Furthermore, by the formulation of the ({}-I) Rule and definition typing
it follows that `S` has the form given in (2).

### Lemma (Corresponding types)

If `Γ ~ s` and `x: T in Γ` then exactly one of the following alternatives applies:
 1. `s(x) = λ(y:S)t` for a term `t` such that `Γ, x: S ⊢ t: U` and `T = ∀(x: S)U`.
 2. `s(x) = new(s:S)d` and `T = μ(x:S)`.

*Proof*: Assume `x: T in Γ`, say `Γ = G1,x:T,G2`.
By the definition of `~`, `G1 ⊢! v: T` for some value `v`.
We distinguish acccording to whether `v` is a `lambda` or `new`.

In the first case, let `v = λ(y: S)t`.
By by definition of `⊢!`, `T` is derived using rule (all-I).
Hence, `T = ∀(x: S)U` for some type `U` such that `G1, x: S ⊢ t: U`.
By (Weakening), `Γ, x: S ⊢ t: U`.

In the second case, let `v = new(x: S)d`
(arranging w.l.o.g by alpha renaming that the bound variable in the new is `x`).
By by definition of `⊢!`, `T` is derived using rule ({}-I).
Hence, `T = μ(x: S)`.

### Lemma (Unique tight bounds)

If `Γ ~ s` and `Γ ⊢! x: {A: T<sub>1</sub>..T<sub>1</sub>}` and `Γ ⊢! x: {A: T<sub>2</sub>..T<sub>2</sub>}` then `T<sub>1</sub> = T<sub>2</sub>`.

*Proof*
Since `Γ ⊢! x: {A: Ti..Ti}` (i = 1,2), `Γ` contains a binding for `x`, say `x: T in Γ`.
By (Corresponding Types) one of the following alternatives applies.

 1. `s(x) = λ(y:S)t` for a term `t` such that `Γ, x: S ⊢ t: U` and `T = ∀(x: S)U`.
    But `x: {A: Ti..Ti)` cannot be derived from `x: ∀(x: S)U` using only (Rec-E) and
    (And-<:), (Trans) subsumption steps, so this alternative is impossible.

 2. `s(x) = new(x:S)d` and `T = μ(x:S)`. By (Corresponding Definition Types),
    `T` is of the form
    `μ(x: S<sub>1</sub> & ... & Sn)` where exactly one `Si` defines a label `A`. Let `Si = {A: U..U}`.
    It follows that `T<sub>1</sub> = U = T<sub>2</sub>`.


### Definition (Tight bound typing)

A typing or subtyping derivation is *tight* in environment `Γ` if
it only contains the following
tight variants of (Sel-<:), (<:-Sel) when `Γ' = Γ`:

    (<:-Sel-tight)
                              Γ' ⊢! x: {A: T..T}
                              -------------------
                                 Γ' ⊢ T <: x.A
    (Sel-<:-tight)
                              Γ' ⊢! x: {A: T..T}
                              -------------------
                                 Γ' ⊢ x.A <: T

For environments that extend Γ, full (Sel-<:) and (<:-Sel) are permitted.

We write `Γ ⊢# t: T` if `Γ ⊢ t: T` with a derivation that is tight in `Γ`.

We write `Γ ⊢# S <: U` if `Γ ⊢ S <: U` with a derivation that is tight in `Γ`.


### Definition (Has member)

A variable `x` with type `T` has a member `A: S..U`
in environment `Γ`, written `Γ ⊢# x: T has A: S..U`, if `Γ ⊢# x: T` and
the judgement is derivable by the following rules.

    (Refl-has)
                        Γ ⊢# x: {A: S..U} has A: S..U
    (&-has)
                           Γ ⊢# x: T<sub>1</sub> has A: S..U
                         ----------------------------
                         Γ ⊢# x: T<sub>1</sub> & T<sub>2</sub> has A: S..U

                           Γ ⊢# x: T<sub>2</sub> has A: S..U
                         ----------------------------
                         Γ ⊢# x: T<sub>1</sub> & T<sub>2</sub> has A: S..U
    (rec-has)
                            Γ ⊢# x: T has A: S..U
                        ------------------------------
                        Γ ⊢# x: μ(x: T) has A: S..U
    (sel-has)
                Γ ⊢! y: {B: T'..T'}   Γ ⊢# x: T' has A: S..U
                ----------------------------------------------
                           Γ ⊢# x: y.B has A: S..U
    (Bot-has)
                        Γ ⊢# x: Bot has A: S..U

### Lemma (Has member inversion)
If `Γ ⊢ x: T has A: S..U` then one of the following cases applies:

 1. `T = {A: S..U}`.
 2. `T = T<sub>1</sub> & T<sub>2</sub>` and `Γ ⊢# x: T<sub>1</sub> has A: S..U` or `Γ ⊢# x: T<sub>2</sub> has A: S..U`.
 3. `T = μ(x: T')` and `Γ ⊢# x: T' has A: S..U`.
 4. `T = y.B` and there exists a type `T'` such that
    `Γ ⊢! y: {B: T'..T'}` and `Γ ⊢# x: T' has A: S..U`.
 5. `T = Bot`.

*Proof:* Direct from the (Has member) rules.

### Lemma (Has member tightness)

If `Γ ~ s` and `s(x) = new(x: T)d` and `Γ ⊢# x: μ(x: T) has A: S..U` then
there is a type `T'` such that `S = T'` and `U = T'`.

*Proof:* By inspection of definition typing.

### Lemma (Has member covariance)
If `Γ ~ s`, `Γ ⊢# T<sub>1</sub> <: T<sub>2</sub>` and `Γ ⊢# x: T<sub>1</sub>` and `Γ ⊢# x: T<sub>2</sub> has A: S<sub>2</sub>..U2` then
there exist types `S<sub>1</sub>`, `U1` such that `Γ ⊢# x: T<sub>1</sub> has A: S<sub>1</sub>..U1`
and `Γ ⊢# S<sub>2</sub> <: S<sub>1</sub>` and `Γ ⊢# U1 <: U2`.

*Proof:* by induction on subtyping derivations.

**Case (<:-Top)**. Does not apply since `Top` cannot appear in a `has` judgement.

**Case (Bot-<:)**. By definition of (Has-member), case (Bot-has).

**Case (Refl-<:)**. Immediate

**Case (Trans-<:)**. Then the last rule is:

                    Γ ⊢# T<sub>1</sub> <: T3   Γ ⊢# T3 <: T<sub>2</sub>
                    -------------------------------
                            Γ ⊢# T<sub>1</sub> <: T<sub>2</sub>

By subsumption, since `Γ ⊢# x: T<sub>1</sub>` we have also `Γ ⊢# x: T3`.
By the I.H. there exist types `S3`, `U3` such that
`Γ ⊢# x: T3 has A: S3..U3` and `Γ ⊢ S<sub>2</sub> <: S3` and `Γ ⊢ U3 <: U2`.
By the I.H. again, `Γ ⊢ x: T<sub>1</sub> has A: S<sub>1</sub>..U1` with `Γ ⊢ S3 <: S<sub>1</sub>` and `Γ ⊢ U1 <: U3`.
By (Trans-<:), `Γ ⊢ S<sub>2</sub> <: S<sub>1</sub>` and `Γ ⊢ U1 <: U2`.

**Case (And-<:)**. Then the last rule is one of the axioms `Γ ⊢# T<sub>2</sub> & U <: T<sub>2</sub>` or
`Γ ⊢# U & T<sub>2</sub> <: T<sub>2</sub>`. Assume the first, the second is analogous. By rule (has-&),
`Γ ⊢# x: T<sub>2</sub> & U has A: S<sub>2</sub>..U2`.

**Case (<:-And)**. Then `T<sub>2</sub> = T<sub>2</sub>1 & T<sub>2</sub>2` and the last rule is:

                  Γ ⊢# T<sub>1</sub> <: T<sub>2</sub>1   Γ ⊢# T<sub>1</sub> <: T<sub>2</sub>2
                  ---------------------------------
                        Γ ⊢# T<sub>1</sub> <: T<sub>2</sub>1 & T<sub>2</sub>2

By (Has member inversion), there exists `i in {1,2}` such that `Γ ⊢# x: T<sub>2</sub>i has A: S<sub>2</sub>..U2`.
By the I.H., `Γ ⊢# x: T<sub>1</sub> has S<sub>2</sub>..U2`.

**Case (Fld-<:-Fld)**. Does not apply since `{a: U}` cannot appear in a `has` judgement.

**Case (Typ-<:-Typ)**. Then `T<sub>1</sub> = {A1: S<sub>1</sub>..U1}` and `T<sub>2</sub> = {A2: S<sub>2</sub>'..U2'}`
and the last rule is:

                  Γ ⊢# S<sub>2</sub>' <: S<sub>1</sub>   Γ ⊢# U1 <: U2'
                  ----------------------------------
                  Γ ⊢# {A: S<sub>1</sub>..U1} <: {A: S<sub>2</sub>'..U2'}

By (Has member inversion) on `T<sub>2</sub>`, `S<sub>2</sub>' = S<sub>2</sub>` and `U2' = U2`.
By definition of (Has member) on `T<sub>1</sub>`, `Γ ⊢# x: T<sub>1</sub> has A: S<sub>1</sub>..U1`.
By inversion of the subtyping rule, the result follows.

**Case (<:-Sel-tight)**. Then `T<sub>2</sub> = y.B` and the last rule is:

                         Γ ⊢! y: {B: T<sub>1</sub>..T<sub>1</sub>}
                         -------------------
                           Γ ⊢# T<sub>1</sub> <: y.B

By (has member inversion), there exists a type `T` such that
`Γ ⊢! y: {B: T..T}` and `Γ ⊢# x: T has A: S<sub>2</sub>..U2`.
By (Unique tight bounds), `T = T<sub>1</sub>`, which proves the case.


**Case (Sel-<:-tight)**. Then `T<sub>1</sub> = y.B` and the last rule is:

                         Γ ⊢! y: {B: T<sub>2</sub>..T<sub>2</sub>}
                         -------------------
                           Γ ⊢# y.B <: T<sub>2</sub>

By definition of (Has member), case (sel-has), the result follows.

**Case (All-<:-All)**. Does not apply since `∀(x:S)T` cannot appear in a `has` judgement.

### Lemma (Has member monotonicity)

If `Γ ~ s` and `s(x) = new(x: T<sub>0</sub>)d` and
`Γ ⊢# x: T has A: S..U` then there exists a type `T<sub>1</sub>` such that
`Γ ⊢# x: μ(x: T<sub>0</sub>) has {A: T<sub>1</sub>..T<sub>1</sub>}`
and `Γ ⊢# S <: T<sub>1</sub>` and `Γ ⊢# T<sub>1</sub> <: U`.

*Proof:* By induction of `Γ ⊢# x: T`.

**Case (Var)**. Then the last rule is

                         Γ, x: T, Γ' ⊢ x: T

Since `Γ ~ s`, `T = μ(x: T<sub>0</sub>)`. By (Has member tightness), there is a type `T<sub>1</sub>` such that
`S = T<sub>1</sub>` and `U = T<sub>1</sub>`.

**Case (Sub)**. Then the last rule is:

                     Γ ⊢# x: T<sub>2</sub>   Γ ⊢# T<sub>2</sub> <: T
                     ---------------------------
                              Γ ⊢# x: T

By (Has member covariance) there are types `S<sub>1</sub>`, `U1` such that
`Γ ⊢ x: T<sub>2</sub> has A: S<sub>1</sub>..T<sub>1</sub>` and `Γ ⊢ S <: S<sub>1</sub>` and `Γ ⊢ U1 <: U`.
By the I.H. there exists a type  `T<sub>1</sub>` such that `Γ ⊢ x: μ(x: T<sub>0</sub>) has {A: T<sub>1</sub>..T<sub>1</sub>}`
and `Γ ⊢ S <: T<sub>1</sub>` and `Γ ⊢ T<sub>1</sub> <: U1`. By (Trans) `Γ ⊢ S <: T<sub>1</sub>` and `Γ ⊢ T<sub>1</sub> <: U`.

**Case (Rec-I)**. Then `T = μ(x: T')` and the last rule is:

                             Γ ⊢# x: T'
                          ------------------
                         Γ ⊢# x: μ(x: T')

By (Has member inversion), `Γ ⊢# x: T' has A: S..U`.
By the I.H., there exists a type `T<sub>1</sub>` such that
`Γ ⊢# x: μ(x: T<sub>0</sub>) has {A: T<sub>1</sub>..T<sub>1</sub>}` and `Γ ⊢# S <: T<sub>1</sub>` and `Γ ⊢# T<sub>1</sub> <: U`.

**Case (Rec-E)**. Then the last rule is:

                          Γ ⊢# x: μ(x: T)
                          -----------------
                              Γ ⊢# x: T

By (has-rec), `Γ ⊢# x: μ(x: T) has A: S..U`.
By the I.H. there exists a type `T<sub>1</sub>` such that
`Γ ⊢# x: μ(x: T<sub>0</sub>) has {A: T<sub>1</sub>..T<sub>1</sub>}` and `Γ ⊢# S <: T<sub>1</sub>` and `Γ ⊢# T<sub>1</sub> <: U`.

**Case (&-I)**. Then `T = T<sub>1</sub> & T<sub>2</sub>` and the last rule is:

                      Γ ⊢# x: T<sub>1</sub>   Γ ⊢# x: T<sub>2</sub>
                      -------------------------
                           Γ ⊢ x: T<sub>1</sub> & T<sub>2</sub>

By (Has member inversion), there exists `i in {1,2}` such that `Γ ⊢# x: Ti has A: S..U`.
By the I.H. there exists a type  `T<sub>1</sub>` such that `Γ ⊢ x: μ(x: T') has {A: T<sub>1</sub>..T<sub>1</sub>}`
and `Γ ⊢ S <: T<sub>1</sub>` and `Γ ⊢ T<sub>1</sub> <: U`.

### Lemma (Tight bound completeness)

If `Γ ~ s` and `s(x) = new(x: T)d` and `Γ ⊢# x: {A: S..U}` then `Γ ⊢# x.A <: U` and `Γ ⊢# S <: x.A`.

*Proof:* Since `Γ ⊢# x: {A: S..U}`, we have also `Γ ⊢# x: {A: S..U} has A: S..U`.
By (Has member monotonicity), there exists a type  `T<sub>1</sub>` such that
`Γ ⊢# x: μ(x: T) has {A: T<sub>1</sub>..T<sub>1</sub>}` and `Γ ⊢# S <: T<sub>1</sub>` and `Γ ⊢# T<sub>1</sub> <: U`.
By (Has member inversion, case 3), `Γ ⊢# x: T has A: T<sub>1</sub>..T<sub>1</sub>`.
By (Corresponding Definition Types) `T` is of the form `S<sub>1</sub> & ... & Sn` where each
`Si` is of the form `{A: Ti..Ti}` or `{a: Ti}`.
By (Has member inversion, case 2), there must exist a `Si` such that
`Γ ⊢ x: Si has A: T<sub>1</sub>..T<sub>1</sub>`.
By (Has member inversion), `Si = {A: T<sub>1</sub>..T<sub>1</sub>}`.
By Definition of (⊢!), `Γ ⊢! x: {A: T<sub>1</sub>..T<sub>1</sub>}`.
By definition of (Sel-<:-tight) and (<:-Sel-tight),
`Γ ⊢# x.A <: T<sub>1</sub>` and `Γ ⊢# T<sub>1</sub> <: x.A`.
By (Trans)
`Γ ⊢# x.A <: U` and `Γ ⊢# S <: x.A`.

### Lemma (All-I Inversion)

If `Γ ⊢! λ(x: S)t: U` then `U = ∀(x: S)T` for some type `T` such that
`Γ, x: S ⊢ t: T`.

### Lemma ({}-I Inversion)

If `Γ ⊢! new(x: T)(d<sub>1</sub> & ... & dn): U` then `U = μ(x: T)` and `T` is of the form `S<sub>1</sub> & ... & Sn`, where each `Si` corresponds to exactly one definition `di` in the following way:

 - if `di = {a = t}` then `Si = {a: T'}` for some `T'` such that `Γ ⊢ t: T'`.
 - if `di = {A = T}` then `Si = {A: T..T}`.

### Definition (Possible types)

For a variable `x`, value `v`, environment `Γ`, the set
`Ts(Γ, x, v)` of possible types of `x` defined as `v` in `Γ` is the smallest set `SS` such that:

 1. If `v = new(x: T)d` then `T` in `SS`.
 2. If `v = new(x: T)d` and `{a = t}` in `d` and `Γ ⊢ t: T'` then `{a: T'} in SS`.
 3. If `v = new(x: T)d` and `{A = T'}` in `d` and `Γ ⊢ S <: T'`, `Γ ⊢ T' <: U`
   then `{A: S..U} in SS`.
 4. If `v = λ(x: S)t` and `Γ, x: S ⊢ t: T` and
    `Γ ⊢ S' <: S` and `Γ, x: S' ⊢ T <: T'` then `∀(x: S')T' in SS`.
 5. If `S<sub>1</sub> in SS` and `S<sub>2</sub> in SS` then `S<sub>1</sub> & S<sub>2</sub> in SS`.
 6. If `S in SS` and `Γ ⊢! y: {A: S..S}` then `y.A in SS`.
 7. If `T in SS` and then `μ(x: T) in SS`.
 8. `Top` in `SS`.

### Lemma (Tight possible types closure)
If `Γ ~ s` and `s(x) = v` then
`Ts(Γ, x, v)` is closed wrt `Γ ⊢# _ <: _`.

*Proof*: Let `SS = Ts(Γ, x, v)`. We show `SS` is closed wrt `Γ ⊢# _ <: _`.

Assume `T<sub>0</sub> in SS` and `Γ ⊢ T<sub>0</sub> <: U<sub>0</sub>`.
We show `U<sub>0</sub> in SS` by an induction on subtyping derivations of `Γ ⊢# T<sub>0</sub> <: U<sub>0</sub>`.

**Case (<:-Top)**. Then `U<sub>0</sub> = Top`. By (rule 8), `Top` in `SS`.

**Case (Bot-<:)**. Does not apply, since assumption `T<sub>0</sub> in SS` cannot hold when `T<sub>0</sub> = Bot`.

**Case (Refl-<:)**. Then `U<sub>0</sub> = T<sub>0</sub>` hence `U<sub>0</sub> in SS`.

**Case (Trans-<:)**. Then last last rule is:

                          Γ ⊢ T<sub>0</sub> <: S   Γ ⊢ S <: U<sub>0</sub>
                          ---------------------------
                                 Γ ⊢ T<sub>0</sub> <: U<sub>0</sub>

Then by the I.H. (twice), `S in SS` and `U<sub>0</sub> in SS`.

**Case (And-<:)**. Then `T<sub>0</sub> = U<sub>0</sub> & S` or `T<sub>0</sub> = S & U<sub>0</sub>` for some type
`T`. Assume the first alternative, the second is analogous. The only ways a type `T & U` can
be part of set `SS` is through rule (1) or (5). If `T<sub>0</sub>` is part of `SS` through rule (1), then `v = new(x: T<sub>0</sub>)d`, for some definitions `d`. By (Corresponding Definition Types) `T<sub>0</sub>` is of the form `S<sub>1</sub> & ... & Sn` where each `Si` corresponds to an atomic definition in `d`, and `U<sub>0</sub>` is the intersection of some subset of the `Si` types.
By rule (2) and (3) each of the `Si` types is in `SS`. Hence by applying
rule (5) as often as necessary, `U<sub>0</sub> in SS`.
If `T<sub>0</sub>` is part of `SS` because of rule (5),
`U<sub>0</sub>` and `S` must both be in `SS`.

**Case (<:-And)**. Then `U<sub>0</sub> = T & U` and `Γ ⊢ T<sub>0</sub> <: T`, `Γ ⊢ T<sub>0</sub> <: U`.
By the I.H. `T` and `U` are in `SS`. Hence, with rule (5), `U<sub>0</sub> in SS`.

**Case (Fld-<:-Fld)**. Then `T<sub>0</sub> = {a: T<sub>1</sub>}` and `U<sub>0</sub> = {a: U1}` for types `T<sub>1</sub>`, `U1` such that
`Γ ⊢ T<sub>1</sub> <: U1`. The only way `T<sub>0</sub>` can be in `SS` is through rule (2),
or rule (1) convertible to rule (2) by `Γ ~ s`. That is,
`v = new(x: T)d` and `{a = t}` in `d` and `Γ ⊢ t: T<sub>1</sub>`. Since `Γ ⊢ T<sub>1</sub> <: U1`
we get with (Sub) that `Γ ⊢ t: U1`. With rule (2), `U<sub>0</sub> in SS`.

**Case (Typ-<:-Typ)** Then `T<sub>0</sub> = {A: T<sub>1</sub>..T<sub>2</sub>}` and `U<sub>0</sub> = {A: U1..U2}` for types
`T<sub>1</sub>`, `T<sub>2</sub>`, `U1`, `U2` such that `Γ ⊢ U1 <: T<sub>1</sub>` and `Γ ⊢ T<sub>2</sub> <: U2`.
The only way `T<sub>0</sub>` can be in `SS` is through rule (3) or rule (1) convertible to
rule (3) by `Γ ~ s`. That is,
`v = new(x: T)d` and `{A = T'}` in `d` and `Γ ⊢ T<sub>1</sub> <: T'`, `Γ ⊢ T' <: T<sub>2</sub>`.
With (Trans), `Γ ⊢ U1 <: T'` and `Γ ⊢ T' <: U2`. With rule (3), `U<sub>0</sub> in SS`.

**Case (<:-Sel-tight)**. Then `U<sub>0</sub> = y.A` for some `y` such that `Γ ⊢! y: {A: T<sub>0</sub>..T<sub>0</sub>}`.
With rule (6), `U<sub>0</sub> in SS`.

**Case (Sel-<:-tight)** Then `T<sub>0</sub> = y.A` for some `y` such that `Γ ⊢! y: {A: U<sub>0</sub>..U<sub>0</sub>}`.
The only way `y.A` can be in `SS` is through rule (6).
That is, there is a type `S in SS` such that
`Γ ⊢! y: {A: S..S}`. By (Unique tight bounds), `U<sub>0</sub> = S`, hence `U<sub>0</sub> in SS`.

**Case (All-<:-All)**. Then `T<sub>0</sub> = ∀(y: T<sub>1</sub>)T<sub>2</sub>` and `U<sub>0</sub> = ∀(y: U1)U2`
for some `T<sub>1</sub>`, `U1` such that `Γ ⊢ U1 <: T<sub>1</sub>` and for some `T<sub>2</sub>`, `U2`
such that `Γ, y: U1 ⊢ T<sub>2</sub> <: U2`. The only way `T<sub>0</sub>` can be in `SS` is
through rule (4). That is, `v = λ(x: T)d` and `Γ ⊢ T<sub>1</sub> <: T` and
`Γ, x: T<sub>1</sub> ⊢ t: T<sub>2</sub>`. By (Narrowing), `Γ, x: U1 ⊢ t: T<sub>2</sub>`. With (Sub),
`Γ, x: U1 ⊢ t: U2`. With (Trans), `Γ ⊢ U1 <: T`. With rule (4),
`∀(x: U1)U2 in SS`.

This concludes the induction. Therefore, `SS` is closed wrt `Γ ⊢# _ <: _`.

### Lemma (Possible types completeness for values)

If `Γ ~ s` and `x = v in s` and  `Γ ⊢! v: T` then `T in Ts(Γ, x, v)`.

*Proof*. Assume first that `v = new(x: S)d`.
By the definition `⊢!`, the proof of `Γ ⊢! v: T` must end in a `{}-I` rule.
By ({}-I Inversion), `T = μ(x: S)`. By rule (1) of (Possible Types), `S in Ts(Γ, x, v)`.
By rule (7) of (Possible Types), `μ(x: S) in Ts(Γ, x, v)`.

Assume now that `v = λ(x: S)t`. By the definition `⊢!`, the proof of `Γ ⊢! v: T` must end in a `All-I` rule. By (All-I Inversion),
`U = ∀(x: S)T` for some type `T` such that `Γ, x: S ⊢ t: T`.
By rule (4) of (Possible Types), `∀(x: S)T in Ts(Γ, x, v)`.


### Lemma (Tight possible types completeness)

If `Γ ~ s` and `x = v in s` and  `Γ ⊢# x: T` then `T in Ts(Γ, x, v)`.

*Proof*: By induction on the derivation of `Γ ⊢# x: T`. The derivation
of `Γ ⊢# x: T` must end in one of the following cases:

**Case (Var)**. Since  `Γ ~ s`, `Γ` contains a binding `x: T` such that `Γ ⊢! v: T`.
By (Possible types completeness for values), `T in Ts(Γ, x, v)`.

**Case (Rec-I)**. Then the last rule is:

                                  Γ ⊢# x: T
                              -----------------
                              Γ ⊢# x: μ(x: T)

By the I.H., `T in Ts(Γ, x, v)`. By rule (7) of (Possible Types), `μ(x: T) in Ts(Γ, x, v)`.

**Case (Rec-E)**. Then the last rule is:

                              Γ ⊢# x: μ(x: T)
                              -----------------
                                  Γ ⊢# x: T

By the I.H., `μ(x: T) in Ts(Γ, x, v)`. The only way a `rec` type can be in `Ts(Γ, x, v)` is through rule (7). Hence, `T in Ts(Γ, x, v)`.

**Case (&-I). Then the last rule is:

                            Γ ⊢# x: T   Γ ⊢# x: U
                            ---------------------
                                Γ ⊢# x: T & U

By the I.H., `T in Ts(Γ, x, v)` and `U in Ts(Γ, x, v)`. By rule (5) of (Possible Types),
`T & U in Ts(Γ, x, v)`.

**Case (Sub)**. Then the last rule is:

                           Γ ⊢# x: T   Γ ⊢# T <: U
                           -----------------------
                                  Γ ⊢# x: U

By the I.H., `T in Ts(Γ, x, v)`. By (Tight possible types closure), `U in Ts(Γ, x, v)`.

### Lemma (Equivalence of `Γ ⊢ ...` and `Γ ⊢# ...`)

`Γ ⊢# ...` to `Γ ⊢ ...` is straightforward by mutual induction on
typing and subtyping derivations.

For `Γ ⊢# ...` to `Γ ⊢ ...`, all cases are straightforward by mutual
induction except tightening subtyping of type selections. We can use
(Tight bound completeness), provided we can show that `Γ ⊢# x :
{A:S..U}` implies that `s(x) = new(x: T)d` for some `T` and `d`, given
also `Γ ~ s`. Since `Γ ~ s`, we know that `s(x) = v` for some
`v`. By (Tight possible types completeness), `{A:S..U} in Ts(Γ, x,
v)`. By inversion, `v` must have of the form `new(x: T)d` for some `T`
and `d`.

### Lemma (Possible types closure)
If `Γ ~ s` and `s(x) = v` then `Ts(Γ, x, v)` is closed wrt `Γ ⊢ _ <: _`.

*Proof*: By (Tight possible types) and (Equivalence of `Γ ⊢ _ <: _` and `Γ ⊢# _ <: _`).

### Lemma (Possible types completeness)

If `Γ ~ s` and `x = v in s` and  `Γ ⊢ x: T` then `T in Ts(Γ, x, v)`.

*Proof*: By (Tight possible types completeness) and (Equivalence of `Γ ⊢ _ : _` and `Γ ⊢# _ : _`).

### Lemma (Possible types)
If `Γ ~ s` and `Γ ⊢ x: T` then, for some value `v`,
`s(x) = v` and `T in Ts(Γ, x, v)`.

*Proof*: If `Γ ⊢ x: T`, `x` must be bound in `Γ`. Since `Γ ~ s` there must be a value `v`
such that `s |= x = v`. By (Possible types completeness), `T in Ts(Γ, x, v)`.

### Lemma (Canonical forms 1)
If `Γ ~ s` and `Γ ⊢ x: ∀(x: T)U` then `s(x) = λ(x: T')t` where
`Γ ⊢ T <: T'` and `Γ, x: T ⊢ t: U`.

Proof: Since `x` has a type in `Γ`, `x` must be bound in `Γ`, say `Γ = G1,x:S,G2`.
Since `Γ ~ s` there exists a value `v` such that `x = v` in `s` and `G1 ⊢ v:S`.
By (Possible Types), `v` cannot be a new because `∀(x: T)U` is ∉ `T(Γ, x, v)`
if `v` is a `new`.
So `v` must be of the form `λ(x: T')t`.
Again by (Possible Types) the only way an `x` defined as a `λ(x: T')t`
can have a type `∀(x: T)U` is
if, for some `U<sub>0</sub>`, `Γ ⊢ T <: T'`, `Γ, x: T' ⊢ t: U<sub>0</sub>` and `Γ, x: T ⊢ U<sub>0</sub> <: U`.
By (Sub) and (Narrowing), `Γ, x: T ⊢ t: U`.

### Lemma (Canonical forms 2)
If `Γ ~ s` and `Γ ⊢ x: {a: T}` then `s(x) = new(x: S)d` for some type `S`,
definition `d` such that
`Γ ⊢ d: S` and `d` contains a definition `{a = t}` where `Γ ⊢ t: T`.

Proof: Since `x` has a type in `Γ`, `x` must be bound in `Γ`, say `Γ = G1,x:S,G2`.
Since `Γ ~ s` there exists a value `v` such that `x = v` in `s` and `G1 ⊢ v:S`.
By (Possible Types) `v` cannot be a lambda because `{a: T}` is ∉ `T(Γ, x, v)`
if `v` is a `lambda`.
So `v` must be of the form `new(x: S)d`.
Again by (Possible Types) the only way an `x` defined as `new(x: S)d` can have a type
`{a: T}` is if there is a definition `{a = t}` in `d` and `Γ ⊢ t: T`.


<!---
### Lemma (Alternative formulation of existential subtyping)

Instead of (Ex-<:) and (<:-Ex) one may equivalently use the three rules below:

    (Ex-<:)
                               (x ∉ fv(T))
                             -------------------
                             Γ ⊢ ex(x: S)T <: T
    (<:-Ex)
                                  Γ ⊢ x: S
                            ---------------------
                             Γ ⊢ T <: ex(x: S)T
    (Ex-<:-Ex)
                     Γ :- S<sub>1</sub> <: S<sub>2</sub>   Γ, x: S<sub>1</sub> ⊢ T<sub>1</sub> <: T<sub>2</sub>
                     ------------------------------------
                       Γ ⊢ ex(x: S<sub>1</sub>)T<sub>1</sub> <: ex(x: S<sub>2</sub>)T<sub>2</sub>

Proof: we can derive each rule in one rule system using the rules of the other.
-->


### Theorem (Preservation)

If `Γ ⊢ t: T` and `Γ ~ s` and `s | t -> s' | t'`, then there exists
an environment `Γ''` such that, letting `Γ' = Γ, Γ''` one has `Γ' ⊢ t': T` and `Γ' ~ s'`.

### Theorem (Progress)

If `Γ ⊢ t: T` and `Γ ~ s` then either

 - `t` is a normal form, or
 - `s | t -> s' | t'`, for some store `s'`, term `t'`.

*Proof*: We prove both theorems together. To be shown:

Let `Γ ⊢ t: T` and `Γ ~ s`. Then either

 - `t` is a normal form, or
 - there exists a store `s'`, term `t'` such that `s | t -> s' | t'`, and
   for any such `s'`, `t'` there exists an environment `Γ''` such that, letting `Γ' = Γ, Γ''` one has
   `Γ' ⊢ t': T` and `Γ' ~ s'`.

The proof is by a induction on typing derivations of `Γ ⊢ t: T`.

If the last rule is one of (Var), (All-I), ({}-I), (Rec-I), (Rec-E), (&-I),
`t` is a normal form and the result follows immediately.

**Case (All-E)**: Then the last rule is:

                       Γ ⊢ x: ∀(z: S)T    Γ ⊢ z: S
                       -------------------------------
                                 Γ ⊢ x y: [z:=y]T

Since `Γ ~ s`, `Γ ⊢ s(x): ∀(z: S)T`. By (Canonical forms 1),
`s(x) = λ(z: S')t` where `Γ ⊢ S <: S'` and `Γ, z: S ⊢ t: T`.
By (Apply), `s | x y ->  s | [z:=y]t`.
By (Subst), Γ ⊢ [z:=y]t: [z:=y]T.

**Case ({}-E)**: Then the last rule is:

                                Γ ⊢ x: {a: T}
                                -------------
                                 Γ ⊢ x.a: T

Since `Γ ~ s`, `Γ ⊢ s(x): {a: T}`. By (Canonical forms 2),
`s(x) = new(y: S)d` for some binding `y = new(y: S)d`, such that `Γ ⊢ d: S` and `d` contains
a definition `{a = t}` where `Γ ⊢ t: T`.
By (Project) `s | x.a -> s | t`, which proves the case.

**Case (Let)**: Then the last rule is:

                Γ ⊢ t: T   Γ, x: T ⊢ u: U   (x ∉ fv(U))
                ----------------------------------------------
                            Γ ⊢ let x = t in u: U

we distinguish according to whether `t` is a value, variable, or general term.

If `t = v` for some value `v`, then by (Let-Value),
`s | let x = v in t --> s, x = v | t`.
Inspection of the type assignment rules shows that
any typing of a `lambda` must contain an (All-I) rule, which can only
be followed by (Sub) steps. Similarly, the typing of a `new` must
contain a ({}-I) rule, which can be only followed by subsumption
steps. Let `T'` be the type obtained for `v` by the (All-I) or ({}-I)
rule and let `D` be the (possibly empty) sequence of subsumption steps
that follows it. Applying a (Var) step on `x` and following with `D`
gives a derivation of `Γ, x: T' ⊢ x: T`.
This means `Γ, x: T' <: Γ, x: T`.
By (Narrowing), `Γ, x: T' ⊢ u: U`.
Furthermore, by the construction of `T'`, `Γ ⊢! v: T'`, hence
`Γ, x: T' ~ s, x = v`.

If `t = y` for some variable `y`, then by (Let-Var)
`s | let x = y in t --> s | [x:=y]t`.
The preconditions of the last rule are then: `Γ ⊢ y: T` and `Γ, x: T ⊢ u: U` and
`x ∉ fv(U)`.
Furthermore, since `fv(T) <= dom(Γ)` and `x ∉ dom(Γ)`, `x ∉ fv(T)`.
It follows with (Subst) that `[x:=y]t: [x:=y]U`. Since `x ∉ fv(U)`, `[x:=y]U = U`,
which proves the case.

If `t` is not a value nor a variable, then by the induction hypothesis
 there exist `s'`, `t'` such that `s | t -> s' | t'` and for any such
 `s'`, `t'` there exists an environment `Γ' = Γ, Γ''` such that `Γ' ⊢
 t': T` and `Γ' ~ s'`. By (Weakening) `Γ, Γ'', x: T ⊢ u: U`. Hence,
 by (Let), `Γ' ⊢ let x = t' in u: U`.

**Case (Sub)**: Then the last rule is:

                           Γ ⊢ t: T   Γ ⊢ T <: U
                           -----------------------
                                  Γ ⊢ t: U

If `t` is a value, the result follows immediately. Assume now that `t` is not a value.
By the induction hypothesis there exist
 `s'`, `t'` such that `s | t -> s' | t'` and for any such `s'`, `t'`
 there exists an environment `Γ' = Γ, Γ''` such that `Γ' ⊢ t': T` and
 `Γ' ~ s'`. By (Weakening, 2nd clause), `Γ' ⊢ T <: U`.
Then by (Sub) it follows that `Γ' ⊢ t: U`.


