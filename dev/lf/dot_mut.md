# Abstract Syntax

    Term member     a, b, c
    Type member     A, B, C
    Variable        x, y, z

    Type     S, T, U = {a: T}                       field declaration
                       {A: S..T}                    type declaration
                       S & T                        intersection
                       x.A                          projection
                       μ(x: T)                      recursive dependent type
                       ∀(x: S)T                     dependent function
                       Top                          top type
                       Bot                          bottom type
                       Ref T                        reference type

    Value          v = ν(x: T)d                     object
                       λ(x: T)t                     lambda abstraction
                       l                            location

    Term     s, t, u = x                            variable
                       v                            value
                       x.a                          selection
                       x y                          application
                       let x = t in u               let
                       ref x T                      reference
                       !x                           dereference
                       x := y                       assignment                

    Definition     d = {a = t}                      field definition
                       {A = T}                      type definition
                       d & d'                       aggregate definition

    Stack          s = ... x = v ...
    Store          σ = ... l = v ...
    Environment    Γ = ... x: T ...
    Store Typing   Σ = ... l: T ...

***

### Evaluation: `s·σ | t -> s'·σ' | t'`

    (Project)
                             s·σ | x.a  -->  s·σ | t          if s(x) = ν(x: T)(d, a = t)
    (Apply)
                             s·σ | x y  -->  s·σ | [z:=y]t    if s(x) = λ(z: T)t
    (Let-Var)
                  s·σ | let x = y in t  -->  s·σ | [x:=y]t
    (Let-Value)
                  s·σ | let x = v in t  -->  (s, x = v)·σ  | t
    (Ctx)
                               s·σ | t  -->  s'·σ' | t'
                  --------------------------------------------------
                  s·σ | let x = t in u  -->  s'·σ' | let x = t' in u

    (Ref-Var)
                                       l ∉ dom(σ)
                            --------------------------------
                            s·σ | ref x --> s·(σ, l = x) | l

    (Asgn)
                                        s(x) = l
                           ---------------------------------
                           s·σ | x := y --> s·(σ, l = y) | v

    (Deref-Var)
                                s(x) = l   σ(l) = y
                               --------------------
                               s·σ | !x --> s·σ | y


***

## Typing Rules

### Type Assignment `Γ | Σ ⊢ t: T`

    (Var)
                            (Γ, x: T, Γ') | Σ ⊢ x: T

    (LOC)
                          Γ | (Σ, l: T, Σ') ⊢ l: Ref T
    
    (All-I)
                       (Γ, x: T) | Σ ⊢ t: U      x ∉ fv(T)
                       -----------------------------------
                          Γ | Σ ⊢ λ(x: T)t: ∀(x: T)U
    
    (All-E)
                       Γ | Σ ⊢ x: ∀(z: S)T    Γ | Σ ⊢ y: S
                       -----------------------------------
                               Γ | Σ ⊢ x y: [z:=y]T
    
    ({}-I)
                             (Γ, x: T) | Σ ⊢ d: T
                          --------------------------
                          Γ | Σ ⊢ ν(x: T)d: μ(x: T)
    
    ({}-E)
                                Γ | Σ ⊢ x: {a: T}
                                -----------------
                                  Γ | Σ ⊢ x.a: T
    
    (Let)
                Γ | Σ ⊢ t: T   (Γ, x: T) | Σ ⊢ u: U     x ∉ fv(U)
                -------------------------------------------------
                            Γ | Σ ⊢ let x = t in u: U
    
    (Rec-I)
                                  Γ | Σ ⊢ x: T
                              -----------------
                              Γ | Σ ⊢ x: μ(x: T)
    
    (Rec-E)
                              Γ | Σ ⊢ x: μ(x: T)
                              -----------------
                                  Γ | Σ ⊢ x: T
    
    (&-I)
                            Γ | Σ ⊢ x: T   Γ | Σ ⊢ x: U
                            ---------------------------
                                Γ | Σ ⊢ x: T & U
    
    (Sub)
                           Γ | Σ ⊢ t: T   Γ | Σ ⊢ T <: U
                           -----------------------------
                                  Γ | Σ ⊢ t: U

    (Ref)                   
                                    Γ | Σ ⊢ x: T
                                -----------------------
                                Γ | Σ ⊢ ref x T: Ref T

    (Deref)
                                Γ | Σ ⊢ x: Ref T
                                ----------------
                                 Γ | Σ ⊢ !x: T

    (Asgn)
                        Γ | Σ ⊢ x: Ref T     Γ | Σ ⊢ y: T
                        ---------------------------------
                                Γ | Σ ⊢ (x := y): T
    

***

### Definition Type Assignment `Γ | Σ ⊢ d: T`

    (Fld-I)
                                  Γ | Σ ⊢ t: T
                             -----------------------
                             Γ | Σ ⊢ {a = t}: {a: T}
    
    (Typ-I)
                           Γ | Σ ⊢ {A = T}: {A: T..T}
    
    (AndDef-I)
           Γ | Σ ⊢ d1: T1   Γ | Σ ⊢ d2: T2   (dom(d1), dom(d2) disjoint)
           -------------------------------------------------------------
                            Γ | Σ ⊢ d1 & d2: T1 & T2


***

### Subtyping: `Γ | Σ ⊢ T <: U`

    (<:-Top)
                                Γ | Σ ⊢ T <: Top
    
    (Bot-<:)
                                Γ | Σ ⊢ Bot <: T
    
    (Refl-<:)
                                Γ | Σ ⊢ T <: T
    
    (Trans-<:)
                          Γ | Σ ⊢ S <: T   Γ | Σ ⊢ T <: U
                          -------------------------------
                                 Γ | Σ ⊢ S <: U
    
    (And-<:)
                               Γ | Σ ⊢ T & U <: T

                               Γ | Σ ⊢ T & U <: U
    
    (<:-And)
                          Γ | Σ ⊢ S <: T   Γ | Σ ⊢ S <: U
                          -------------------------------
                                  S <: T & U
    
    (Fld-<:-Fld)
                                 Γ | Σ ⊢ T <: U
                            ------------------------
                            Γ | Σ ⊢ {a: T} <: {a: U}
    
    (Typ-<:-Typ)
                        Γ | Σ ⊢ S2 <: S1   Γ | Σ ⊢ T1 <: T2
                       ------------------------------------
                        Γ | Σ ⊢ {A: S1..T1} <: {A: S2..T2}
    
    (<:-Sel)
                              Γ | Σ ⊢ x: {A: S..T}
                              --------------------
                                Γ | Σ ⊢ S <: x.A
    
    (Sel-<:)
                              Γ | Σ ⊢ x: {A: S..T}
                              --------------------
                               Γ | Σ ⊢ x.A <: T
    
    (All-<:-All)
                     Γ | Σ ⊢ S2 <: S1   Γ, x: S2 | Σ ⊢ T1 <: T2
                     ------------------------------------------
                          Γ | Σ ⊢ ∀(x: S1)T1 <: ∀(x: S2)T2


*Note:* `Γ, x: T` is well-defined only if `x` is neither in the domain of `Γ` nor in
its free variables.



