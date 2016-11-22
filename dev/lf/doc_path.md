# DOT With Expanded Paths

## Abstract Syntax

    Term member     a, b, c
    Type member     A, B, C
    Variable        x, y, z

    Path           p = x			    path variable			new
                       p.a			    path selection			new

    Type     S, T, U = {a: T}                       field declaration
                       {a:! T}                      pathable field declaration		new
                       {A: S..T}                    type declaration
                       S & T                        intersection
                       p.A                          projection				change
                       μ(x: T)                      recursive dependent type
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
                            Γ, x: T, Γ' ⊢ x:! T						change


    (Path)                      Г ⊢  p:! {a:! T}
                                ----------------					new
                                   Г ⊢ p.a:! T


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

### Definition Type Assignment `Γ; z: T ⊢ d: T`						change (z denotes recursive variable)

    (Fld-I)
                                  Γ; z: T ⊢ t: T
                             -------------------------
                             Γ; z: T ⊢ {a = t}: {a: T}

    (Fld-Path-I)
                                    Г ⊢ p:! U
                             --------------------------					new
                             Г; z: T ⊢ {a = p}: {a:! U}

    (Typ-I)
                           Γ; z: T ⊢ {A = T}: {A: T..T}

    (AndDef-I)
           Γ; z: T ⊢ d1: T1   Γ; z: T ⊢ d2: T2   (dom(d1), dom(d2) disjoint)
           -----------------------------------------------------------------
                            Γ; z: T ⊢ d1 & d2: T1 & T2


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

    (Path-<:)		   
    			   Г ⊢ {a:! T} <: {a: T}					new


*Note:* `Γ, x: T` is well-defined only if `x` is neither in the domain of `Γ` nor in
its free variables.
