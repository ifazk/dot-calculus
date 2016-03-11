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
           Γ ⊢ d1: T1   Γ ⊢ d2: T2   (dom(d1), dom(d2) disjoint)
           -------------------------------------------------------
                            Γ ⊢ d1 & d2: T1 & T2


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
                        Γ ⊢ S2 <: S1   Γ ⊢ T1 <: T2
                       -------------------------------
                       Γ ⊢ {A: S1..T1} <: {A: S2..T2}
    (<:-Sel)
                              Γ ⊢ x: {A: S..T}
                              -----------------
                                Γ ⊢ S <: x.A
    (Sel-<:)
                              Γ ⊢ x: {A: S..T}
                              -----------------
                               Γ ⊢ x.A <: T
    (All-<:-All)
                     Γ ⊢ S2 <: S1   Γ, x: S2 ⊢ T1 <: T2
                     ------------------------------------
                      Γ ⊢ ∀(x: S1)T1 <: ∀(x: S2)T2


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
     new { z => d1; ...; dn }  ===  new(x: D1 & ... & Dn)d1 & ... & dn
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
Let [s] be a renaming `[x0:=y0]` for arbitrary variables `x0`, `y0`. Then

 - `     [s]μ(x: T)  =  μ([s]x: [s]T)`
 - `    [s]∀(x: T)U  =  ∀([s]x: [s]T): [s]U`
 - `    [s]new(x: T)d  =  new([s]x: [s]T): [s]d`
 - ` [s]λ(x: T)t  =  λ([s]x: [s]T): [s]t`
 - `[s]let x = t in u  =  let [s]x = [s]t in [s]u`

*Proof*. We prove the first equation; the others are analogous. We distinguish whether or not `x0 = x`.

If `x0 = x` then

      [s]μ(x0: T)
    = (by definition of substitution)
      μ(x0: T)
    = (by alpha renaming x0 to y0)
      μ(y0: [y0:=x0]T)
    = (by rewriting)
      μ([s]x0: [s]T)

If `x0 != x` then

      [s]μ(x: T)
    = (by definition of substitution)
      μ(x: [s]T)
    = (since x0 != x)
      μ([s]x0: [s]T)

### Lemma (Subst)
 1. If `Γ, x: S ⊢ t: T` and `Γ ⊢ y: [x:=y]S`
then `Γ ⊢ [x:=y]t: [x:=y]T`.
 2. If `Γ, x: S ⊢ d: T` and `Γ ⊢ y: [x:=y]S`
then `Γ ⊢ [x:=y]d: [x:=y]T`.

We prove the more general proposition:

If `Γ, x: S, Γ' ⊢ t: T` and `Γ, [x:=y]Γ' ⊢ y: [x:=y]S`, then
`Γ, [x:=y]Γ' ⊢ [x:=y]t: [x:=y]T`. (and the same for `d` instead of `t`).

Proof by mutual induction on derivations.
Let `[s] = [x0:=y0]`.
Assume `Γ, x0: S0, Γ' ⊢ t0: T0` and `Γ, [s]Γ' ⊢ y0: [s]S0`.
To show: `Γ, [s]Γ' ⊢ [s]t0: [s]T0`.

We distinguish according to the last rule in the derivation of `Γ, x0: S0, Γ' ⊢ t0: T0`

**Case (Var)**: We have in this case: `t = x0`, `T0 = S0`,
`Γ, x0: S0, Γ' ⊢ x: S0`, and `Γ, [s]Γ' ⊢ y0: [s]S0`.
Together, `Γ, x0: S0, Γ' ⊢ [s]x0: [s]S0`.

**Case (All-I)** Then `t0 = λ(x: T)t` and the last rule is

                     Γ, x0: S0, Γ', x: T ⊢ t: U
              ------------------------------------------
              Γ, x0: S0, Γ' ⊢ λ(x: T)t: ∀(x: T)U

By the I.H., `Γ, [s]Γ', [s]x: [s]T ⊢ [s]t: [s]U`.
By (All-I), `Γ, [s]Γ' ⊢ λ([s]x: [s]T)[s]t): ∀([s]x: [s]T)[s]U`.
By applying Lemma (Renaming) twice to the RHS, `Γ, [s]Γ' ⊢ [s]λ(x: T)t): [s]∀(x: T)U`.

**Case (All-E)** Then `t0 = x y` and the last rule is

       Γ, x0: S0, Γ' ⊢ x: ∀(y: S)T    Γ, x0: S0, Γ' ⊢ y: S
       -------------------------------------------------------
                    Γ, x0: S0, Γ' ⊢ x y: [z:=y]T

By the. I.H., `Γ, [s]Γ' ⊢ [s]x: ∀(z: [s]S)[s]T` and `Γ, [s]Γ' ⊢ [s]y: [s]S`.
By (All-E), `Γ, [s]Γ' ⊢ [s]x [s]y: [z:=[s]y][s]T`.
W.l.o.g choose `z` so that `z != x0`, `z != y`.
Hence, `[z:=[s]z][s]` = [s][z:=y]. Together,
`Γ,[s]Γ' ⊢ [s](x y): [s][z:=y]T`.

**Case ({}-I)**: Then `t0 = new(x: T)d` and the last rule is

                     Γ, x0: S0, Γ', x: T ⊢ d: T
                --------------------------------------
                Γ, x0: S0, Γ' ⊢ new(x: T)d: μ(x: T)

By the I.H., `Γ, [s]Γ', [s]x: [s]T ⊢ [s]d: [s]T`.
By ({}-I), `Γ, [s]Γ' ⊢ new([s]x: [s]T)[s]d: μ([s]x: [s]T)`
By applying Lemma (Renaming) twice to the RHS,
`Γ, [s]Γ' ⊢ [s]new(x: T)d: [s]μ(x: T)`.

**Case ({}-E)** Then `t0 = x.a` and the last rule is:

                     Γ, x0: S0, Γ' ⊢ x: {a: T}
                     ---------------------------
                       Γ, x0: S0, Γ' ⊢ x.a: T

By the I.H., `Γ, [s]Γ' ⊢ [s]x: {a: [s]T}`.
By ({}-E), `Γ, [s]Γ' ⊢ [s]x.a: [s]T`.

**Case (Let)**: Then `t0 = let x = t in u` and the last rule is:

    Γ, x0: S0, Γ' ⊢ t: T   Γ, x0: S0, Γ', x: T ⊢ u: U   (x ∉ fv(U))
    ----------------------------------------------------------------------
                      Γ, x0: S0, Γ' ⊢ let x = t in u: U

By the I.H., `Γ, [s]Γ' ⊢ [s]t: [s]T` and `Γ, [s]Γ', [s]x: [s]T ⊢ [s]u: [s]U`.
With (Let) it follows that `Γ, [s]Γ' ⊢ let [s]x = [s]t in [s]u: [s]U`.
By (Renaming), `Γ, [s]Γ' ⊢ [s]let x = t in u: [s]U`.

**Case (Rec-I)**: Then `t0 = x` and the last rule is:

                              Γ ⊢ x: T
                          -----------------
                          Γ ⊢ x: μ(x: T)

By the I.H., `Γ, [s]Γ' ⊢ [s]x: [s]T`.
By (Rec-I), `Γ, [s]Γ' ⊢ [s]x: μ([s]x: [s]T)`.
By applying Lemma (Renaming) to the `rec` term, `Γ, [s]Γ' ⊢ [s]x: [s]μ(x: T)`.

**Case (Rec-E)**: Then `t0 = x` and the last rule is:

                    Γ, x0: S0, Γ' ⊢ x: μ(x: T)
                    -----------------------------
                        Γ, x0: S0, Γ' ⊢ x: T

By the I.H., `Γ, [s]Γ' ⊢ [s]x: [s]μ(x: T)`.
By applying Lemma (Renaming) to the `rec` term, `Γ, [s]Γ' ⊢ [s]x: μ([s]x: [s]T)`.
By (Rec-E), `Γ, [s]Γ' ⊢ [s]x: [s]T`.

**Case (&=I)**. Then `t0 = x` amd the last rule is:

                        Γ ⊢ x: T   Γ ⊢ x: U
                        ---------------------
                            Γ ⊢ x: T & U

By the I.H., `Γ, [s]Γ' ⊢ [s]x: [s]T` and `Γ, [s]Γ' ⊢ [s]x: [s]U`.
By (&=I), `Γ, [s]Γ' ⊢ [s]x: [s]T & [s]U`.

**Case (Sub)** Then `t0 = t` and the last rule is:

           Γ, x0: S0, Γ' ⊢ t: T   Γ, x0: S0, Γ' ⊢ T <: U
           -----------------------------------------------
                        Γ, x0: S0, Γ' ⊢ t: U

By the I.H., `Γ, [s]Γ' ⊢ [s]t: [s]T`.
By (Subst-<:), `Γ, [s]Γ' ⊢ [s]T <: [s]U`.
By (Sub), `Γ, [s]Γ' ⊢ [s]T: [s]U`.

**Case (Fld)**. Then `t0 = {a = t}` and the last rule is:

                        Γ, x0: S0, Γ' ⊢ t: S
                   --------------------------------
                   Γ, x0: S0, Γ' ⊢ {a = t}: {a: T}

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
Let [s] = [x0:=y0].
Assume `Γ, x0: S0, Γ' ⊢ T0 <: U0` and `Γ, [s]Γ' ⊢ y0: [s]S0`.
To show: `Γ [s]Γ' ⊢ [s]T0 <: [s]U0`.

We only show two cases; the others are similar.

**Case(<:-Sel)**: Then `T0 = S` and the last rule of `D` is:

                    Γ, x0: S0, Γ' ⊢ x: {A: S..T}
                    -----------------------------
                      Γ, x0: S0, Γ' ⊢ S <: x.A

By the I.H., `Γ, [s]Γ' ⊢ [s]x: {A: [s]S..[s]T}`.
By (<:-Sel), `Γ, [s]Γ' ⊢ [s]S <: [s]x.A`.

**Case (All-<:-All)** Then `T0 = ∀(x: S1)T1` and the last rule is:

     Γ, x0: S0, Γ' ⊢ S2 <: S1   Γ, x0: S0, Γ', x: S2 ⊢ T1 <: T2
     ------------------------------------------------------------
            Γ, x0: S0, Γ' ⊢ ∀(x: S1)T1 <: ∀(x: S2)T2

By the I.H., `Γ, [s]Γ' ⊢ [s]S2 <: [s]S1` and
`Γ, [s]Γ', [s]x: [s]S2 ⊢ [s]T1 <: [s]T2`.
By (All-<:-All), `Γ, [s]Γ' ⊢ ∀([s]x: [s]S1)[s]T1 <: ∀([s]x: [s]S1)[s]T1`.
By (Renaming), `Γ, [s]Γ' ⊢ [s]∀(x: S1)T1 <: [s]∀(x: S2)T2`.


### Lemma (Corresponding Definition Types)

If `Γ ~ s` and `s(x) = new(x: S)d` for some definitions `d = d1 & ... & dn` then
 1. `x: μ(x: S) in Γ`.
 2. `S = S1 & ... & Sn` where for each `i` either

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

If `Γ ~ s` and `Γ ⊢! x: {A: T1..T1}` and `Γ ⊢! x: {A: T2..T2}` then `T1 = T2`.

*Proof*
Since `Γ ⊢! x: {A: Ti..Ti}` (i = 1,2), `Γ` contains a binding for `x`, say `x: T in Γ`.
By (Corresponding Types) one of the following alternatives applies.

 1. `s(x) = λ(y:S)t` for a term `t` such that `Γ, x: S ⊢ t: U` and `T = ∀(x: S)U`.
    But `x: {A: Ti..Ti)` cannot be derived from `x: ∀(x: S)U` using only (Rec-E) and
    (And-<:), (Trans) subsumption steps, so this alternative is impossible.

 2. `s(x) = new(x:S)d` and `T = μ(x:S)`. By (Corresponding Definition Types),
    `T` is of the form
    `μ(x: S1 & ... & Sn)` where exactly one `Si` defines a label `A`. Let `Si = {A: U..U}`.
    It follows that `T1 = U = T2`.


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
                           Γ ⊢# x: T1 has A: S..U
                         ----------------------------
                         Γ ⊢# x: T1 & T2 has A: S..U

                           Γ ⊢# x: T2 has A: S..U
                         ----------------------------
                         Γ ⊢# x: T1 & T2 has A: S..U
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
 2. `T = T1 & T2` and `Γ ⊢# x: T1 has A: S..U` or `Γ ⊢# x: T2 has A: S..U`.
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
If `Γ ~ s`, `Γ ⊢# T1 <: T2` and `Γ ⊢# x: T1` and `Γ ⊢# x: T2 has A: S2..U2` then
there exist types `S1`, `U1` such that `Γ ⊢# x: T1 has A: S1..U1`
and `Γ ⊢# S2 <: S1` and `Γ ⊢# U1 <: U2`.

*Proof:* by induction on subtyping derivations.

**Case (<:-Top)**. Does not apply since `Top` cannot appear in a `has` judgement.

**Case (Bot-<:)**. By definition of (Has-member), case (Bot-has).

**Case (Refl-<:)**. Immediate

**Case (Trans-<:)**. Then the last rule is:

                    Γ ⊢# T1 <: T3   Γ ⊢# T3 <: T2
                    -------------------------------
                            Γ ⊢# T1 <: T2

By subsumption, since `Γ ⊢# x: T1` we have also `Γ ⊢# x: T3`.
By the I.H. there exist types `S3`, `U3` such that
`Γ ⊢# x: T3 has A: S3..U3` and `Γ ⊢ S2 <: S3` and `Γ ⊢ U3 <: U2`.
By the I.H. again, `Γ ⊢ x: T1 has A: S1..U1` with `Γ ⊢ S3 <: S1` and `Γ ⊢ U1 <: U3`.
By (Trans-<:), `Γ ⊢ S2 <: S1` and `Γ ⊢ U1 <: U2`.

**Case (And-<:)**. Then the last rule is one of the axioms `Γ ⊢# T2 & U <: T2` or
`Γ ⊢# U & T2 <: T2`. Assume the first, the second is analogous. By rule (has-&),
`Γ ⊢# x: T2 & U has A: S2..U2`.

**Case (<:-And)**. Then `T2 = T21 & T22` and the last rule is:

                  Γ ⊢# T1 <: T21   Γ ⊢# T1 <: T22
                  ---------------------------------
                        Γ ⊢# T1 <: T21 & T22

By (Has member inversion), there exists `i in {1,2}` such that `Γ ⊢# x: T2i has A: S2..U2`.
By the I.H., `Γ ⊢# x: T1 has S2..U2`.

**Case (Fld-<:-Fld)**. Does not apply since `{a: U}` cannot appear in a `has` judgement.

**Case (Typ-<:-Typ)**. Then `T1 = {A1: S1..U1}` and `T2 = {A2: S2'..U2'}`
and the last rule is:

                  Γ ⊢# S2' <: S1   Γ ⊢# U1 <: U2'
                  ----------------------------------
                  Γ ⊢# {A: S1..U1} <: {A: S2'..U2'}

By (Has member inversion) on `T2`, `S2' = S2` and `U2' = U2`.
By definition of (Has member) on `T1`, `Γ ⊢# x: T1 has A: S1..U1`.
By inversion of the subtyping rule, the result follows.

**Case (<:-Sel-tight)**. Then `T2 = y.B` and the last rule is:

                         Γ ⊢! y: {B: T1..T1}
                         -------------------
                           Γ ⊢# T1 <: y.B

By (has member inversion), there exists a type `T` such that
`Γ ⊢! y: {B: T..T}` and `Γ ⊢# x: T has A: S2..U2`.
By (Unique tight bounds), `T = T1`, which proves the case.


**Case (Sel-<:-tight)**. Then `T1 = y.B` and the last rule is:

                         Γ ⊢! y: {B: T2..T2}
                         -------------------
                           Γ ⊢# y.B <: T2

By definition of (Has member), case (sel-has), the result follows.

**Case (All-<:-All)**. Does not apply since `∀(x:S)T` cannot appear in a `has` judgement.

### Lemma (Has member monotonicity)

If `Γ ~ s` and `s(x) = new(x: T0)d` and
`Γ ⊢# x: T has A: S..U` then there exists a type `T1` such that
`Γ ⊢# x: μ(x: T0) has {A: T1..T1}`
and `Γ ⊢# S <: T1` and `Γ ⊢# T1 <: U`.

*Proof:* By induction of `Γ ⊢# x: T`.

**Case (Var)**. Then the last rule is

                         Γ, x: T, Γ' ⊢ x: T

Since `Γ ~ s`, `T = μ(x: T0)`. By (Has member tightness), there is a type `T1` such that
`S = T1` and `U = T1`.

**Case (Sub)**. Then the last rule is:

                     Γ ⊢# x: T2   Γ ⊢# T2 <: T
                     ---------------------------
                              Γ ⊢# x: T

By (Has member covariance) there are types `S1`, `U1` such that
`Γ ⊢ x: T2 has A: S1..T1` and `Γ ⊢ S <: S1` and `Γ ⊢ U1 <: U`.
By the I.H. there exists a type  `T1` such that `Γ ⊢ x: μ(x: T0) has {A: T1..T1}`
and `Γ ⊢ S <: T1` and `Γ ⊢ T1 <: U1`. By (Trans) `Γ ⊢ S <: T1` and `Γ ⊢ T1 <: U`.

**Case (Rec-I)**. Then `T = μ(x: T')` and the last rule is:

                             Γ ⊢# x: T'
                          ------------------
                         Γ ⊢# x: μ(x: T')

By (Has member inversion), `Γ ⊢# x: T' has A: S..U`.
By the I.H., there exists a type `T1` such that
`Γ ⊢# x: μ(x: T0) has {A: T1..T1}` and `Γ ⊢# S <: T1` and `Γ ⊢# T1 <: U`.

**Case (Rec-E)**. Then the last rule is:

                          Γ ⊢# x: μ(x: T)
                          -----------------
                              Γ ⊢# x: T

By (has-rec), `Γ ⊢# x: μ(x: T) has A: S..U`.
By the I.H. there exists a type `T1` such that
`Γ ⊢# x: μ(x: T0) has {A: T1..T1}` and `Γ ⊢# S <: T1` and `Γ ⊢# T1 <: U`.

**Case (&-I)**. Then `T = T1 & T2` and the last rule is:

                      Γ ⊢# x: T1   Γ ⊢# x: T2
                      -------------------------
                           Γ ⊢ x: T1 & T2

By (Has member inversion), there exists `i in {1,2}` such that `Γ ⊢# x: Ti has A: S..U`.
By the I.H. there exists a type  `T1` such that `Γ ⊢ x: μ(x: T') has {A: T1..T1}`
and `Γ ⊢ S <: T1` and `Γ ⊢ T1 <: U`.

### Lemma (Tight bound completeness)

If `Γ ~ s` and `s(x) = new(x: T)d` and `Γ ⊢# x: {A: S..U}` then `Γ ⊢# x.A <: U` and `Γ ⊢# S <: x.A`.

*Proof:* Since `Γ ⊢# x: {A: S..U}`, we have also `Γ ⊢# x: {A: S..U} has A: S..U`.
By (Has member monotonicity), there exists a type  `T1` such that
`Γ ⊢# x: μ(x: T) has {A: T1..T1}` and `Γ ⊢# S <: T1` and `Γ ⊢# T1 <: U`.
By (Has member inversion, case 3), `Γ ⊢# x: T has A: T1..T1`.
By (Corresponding Definition Types) `T` is of the form `S1 & ... & Sn` where each
`Si` is of the form `{A: Ti..Ti}` or `{a: Ti}`.
By (Has member inversion, case 2), there must exist a `Si` such that
`Γ ⊢ x: Si has A: T1..T1`.
By (Has member inversion), `Si = {A: T1..T1}`.
By Definition of (⊢!), `Γ ⊢! x: {A: T1..T1}`.
By definition of (Sel-<:-tight) and (<:-Sel-tight),
`Γ ⊢# x.A <: T1` and `Γ ⊢# T1 <: x.A`.
By (Trans)
`Γ ⊢# x.A <: U` and `Γ ⊢# S <: x.A`.

### Lemma (All-I Inversion)

If `Γ ⊢! λ(x: S)t: U` then `U = ∀(x: S)T` for some type `T` such that
`Γ, x: S ⊢ t: T`.

### Lemma ({}-I Inversion)

If `Γ ⊢! new(x: T)(d1 & ... & dn): U` then `U = μ(x: T)` and `T` is of the form `S1 & ... & Sn`, where each `Si` corresponds to exactly one definition `di` in the following way:

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
 5. If `S1 in SS` and `S2 in SS` then `S1 & S2 in SS`.
 6. If `S in SS` and `Γ ⊢! y: {A: S..S}` then `y.A in SS`.
 7. If `T in SS` and then `μ(x: T) in SS`.
 8. `Top` in `SS`.

### Lemma (Tight possible types closure)
If `Γ ~ s` and `s(x) = v` then
`Ts(Γ, x, v)` is closed wrt `Γ ⊢# _ <: _`.

*Proof*: Let `SS = Ts(Γ, x, v)`. We show `SS` is closed wrt `Γ ⊢# _ <: _`.

Assume `T0 in SS` and `Γ ⊢ T0 <: U0`.
We show `U0 in SS` by an induction on subtyping derivations of `Γ ⊢# T0 <: U0`.

**Case (<:-Top)**. Then `U0 = Top`. By (rule 8), `Top` in `SS`.

**Case (Bot-<:)**. Does not apply, since assumption `T0 in SS` cannot hold when `T0 = Bot`.

**Case (Refl-<:)**. Then `U0 = T0` hence `U0 in SS`.

**Case (Trans-<:)**. Then last last rule is:

                          Γ ⊢ T0 <: S   Γ ⊢ S <: U0
                          ---------------------------
                                 Γ ⊢ T0 <: U0

Then by the I.H. (twice), `S in SS` and `U0 in SS`.

**Case (And-<:)**. Then `T0 = U0 & S` or `T0 = S & U0` for some type
`T`. Assume the first alternative, the second is analogous. The only ways a type `T & U` can
be part of set `SS` is through rule (1) or (5). If `T0` is part of `SS` through rule (1), then `v = new(x: T0)d`, for some definitions `d`. By (Corresponding Definition Types) `T0` is of the form `S1 & ... & Sn` where each `Si` corresponds to an atomic definition in `d`, and `U0` is the intersection of some subset of the `Si` types.
By rule (2) and (3) each of the `Si` types is in `SS`. Hence by applying
rule (5) as often as necessary, `U0 in SS`.
If `T0` is part of `SS` because of rule (5),
`U0` and `S` must both be in `SS`.

**Case (<:-And)**. Then `U0 = T & U` and `Γ ⊢ T0 <: T`, `Γ ⊢ T0 <: U`.
By the I.H. `T` and `U` are in `SS`. Hence, with rule (5), `U0 in SS`.

**Case (Fld-<:-Fld)**. Then `T0 = {a: T1}` and `U0 = {a: U1}` for types `T1`, `U1` such that
`Γ ⊢ T1 <: U1`. The only way `T0` can be in `SS` is through rule (2),
or rule (1) convertible to rule (2) by `Γ ~ s`. That is,
`v = new(x: T)d` and `{a = t}` in `d` and `Γ ⊢ t: T1`. Since `Γ ⊢ T1 <: U1`
we get with (Sub) that `Γ ⊢ t: U1`. With rule (2), `U0 in SS`.

**Case (Typ-<:-Typ)** Then `T0 = {A: T1..T2}` and `U0 = {A: U1..U2}` for types
`T1`, `T2`, `U1`, `U2` such that `Γ ⊢ U1 <: T1` and `Γ ⊢ T2 <: U2`.
The only way `T0` can be in `SS` is through rule (3) or rule (1) convertible to
rule (3) by `Γ ~ s`. That is,
`v = new(x: T)d` and `{A = T'}` in `d` and `Γ ⊢ T1 <: T'`, `Γ ⊢ T' <: T2`.
With (Trans), `Γ ⊢ U1 <: T'` and `Γ ⊢ T' <: U2`. With rule (3), `U0 in SS`.

**Case (<:-Sel-tight)**. Then `U0 = y.A` for some `y` such that `Γ ⊢! y: {A: T0..T0}`.
With rule (6), `U0 in SS`.

**Case (Sel-<:-tight)** Then `T0 = y.A` for some `y` such that `Γ ⊢! y: {A: U0..U0}`.
The only way `y.A` can be in `SS` is through rule (6).
That is, there is a type `S in SS` such that
`Γ ⊢! y: {A: S..S}`. By (Unique tight bounds), `U0 = S`, hence `U0 in SS`.

**Case (All-<:-All)**. Then `T0 = ∀(y: T1)T2` and `U0 = ∀(y: U1)U2`
for some `T1`, `U1` such that `Γ ⊢ U1 <: T1` and for some `T2`, `U2`
such that `Γ, y: U1 ⊢ T2 <: U2`. The only way `T0` can be in `SS` is
through rule (4). That is, `v = λ(x: T)d` and `Γ ⊢ T1 <: T` and
`Γ, x: T1 ⊢ t: T2`. By (Narrowing), `Γ, x: U1 ⊢ t: T2`. With (Sub),
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
if, for some `U0`, `Γ ⊢ T <: T'`, `Γ, x: T' ⊢ t: U0` and `Γ, x: T ⊢ U0 <: U`.
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
                     Γ :- S1 <: S2   Γ, x: S1 ⊢ T1 <: T2
                     ------------------------------------
                       Γ ⊢ ex(x: S1)T1 <: ex(x: S2)T2

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



