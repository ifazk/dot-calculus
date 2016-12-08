# Mutable WadlerFest DOT

For details see our [technical report](https://arxiv.org/abs/1611.07610).

## Abstract syntax

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

    Stack          γ = ... x = v ...
    Store          σ = ... l = v ...
    Environment    Γ = ... x: T ...
    Store Typing   Σ = ... l: T ...


In the paper, the abstract syntax is shown in Figure 1.

In the proof, variables are represented using the inductive `avar` type, which can refer to a named or de Bruin indexed variable. The stack γ is represented using `stack`, which is a list of pairs of variables and values. The mutable store σ is represented using `store`, a map from addresses (locations) to variables. The type environment Γ is a list of pairs of variables and types `ctx`, and the store typing Σ is a list `store` of pairs of addresses and types.

Types are represented using the datatype `typ`, terms using `trm`.



## Reduction Rules `γ·σ | t -> γ'·σ' | t'`

    (Project)
                             γ·σ | x.a  -->  γ·σ | t          if γ(x) = ν(x: T)(d, a = t)
    (Apply)
                             γ·σ | x y  -->  γ·σ | [z:=y]t    if γ(x) = λ(z: T)t
    (Let-Var)
                  γ·σ | let x = y in t  -->  γ·σ | [x:=y]t
    (Let-Value)
                  γ·σ | let x = v in t  -->  (γ, x = v)·σ  | t
    (Ctx)
                               γ·σ | t  -->  γ'·σ' | t'
                  --------------------------------------------------
                  γ·σ | let x = t in u  -->  γ'·σ' | let x = t' in u

    (Ref-Var)
                                       l ∉ dom(σ)
                            --------------------------------
                            γ·σ | ref x --> γ·(σ, l = x) | l

    (Asgn)
                                        γ(x) = l
                           ---------------------------------
                           γ·σ | x := y --> γ·(σ, l = y) | v

    (Deref-Var)
                                γ(x) = l   σ(l) = y
                               --------------------
                               γ·σ | !x --> γ·σ | y


In the paper, the reduction rules are shown in Figure 5.

In the proof, the operational semantics is defined in the inductive relation `red`. 
`red γ σ t γ' σ' t'` denotes the reduction step σ|γ|t ⟼  σ'|γ'|t'.

## Type Rules

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

### Subtyping `Γ | Σ ⊢ T <: U`

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


The typing and subtyping rules are depicted in Figures 4 and 5 of the paper.

In the proof, they are defined through mutually inductive definitions `ty_trm`, `ty_def`, `ty_defs`, and `subtyp`. A typing relation is characterized using two modes: 
- `tymode`, which can be `ty_precise` or `ty_general` (precise or general typing), and
- `submode`, which can be `sub_tight` or `sub_general` (tight or general subtyping).

`ty_trm m₁ m₂ Γ Σ t T` corresponds to the typing relation Γ, Σ ⊢ t: T with typing and subtyping modes m₁ and m₂.

`ty_def Γ Σ d D` denotes that the the type declaration of definition `d` is `D`. `ty_defs` allows to reason about multiple the type assignments for multiple definitions in an intersection type.

`subtyp m₁ m₂ Γ Σ T U` corresponds to the subtyping relation Γ, Σ ⊢ T <: U with modes m₁ and m₂.

## Stack Correspondence and Well-Typedness

A stack that corresponds to an environment, written in the paper as Γ, Σ ~ γ, is expressed using the inductive relation `wf_stack`: `wf_stack Γ Σ γ`.

A well-typed store, denoted as Γ, Σ ⊢ σ, is expressed using the inductive relation `wt_store`: `wt_store Γ Σ γ`.

## Type Safety Proof

### Canonical Forms Lemma

There are three canonical-forms lemmas corresponding to Lemma 1 in the paper, one for each type of values.

1) `canonical_forms_1`

  If Γ, Σ ⊢ x: ∀(x: T)U then γ(x)=λ(x: T').t for some T' and t such that 
  - Γ, Σ ⊢ T <: T',
  - (Γ, x: T), Σ ⊢ t: U.

2) `canonical_forms_2`

  If Γ, Σ ⊢ x: {a: T} then γ(x)=ν(x: S)d for some S, d, t such that
  - Γ, Σ ⊢ d: S,
  - {a = t} ∈ d,
  - Γ, Σ ⊢ t: T.

3) `canonical_forms_3`

  If Γ, Σ ⊢ x: Ref T then γ(x)=l and σ(l)=y for some l, y such that
  - Γ, Σ ⊢ l: Ref T,
  - Γ, Σ ⊢ y: T.

### Substitution

The substitution principle (Lemma 2) in the proof is expressed in the Coq lemma `subst_rules`. It consists of the conjunction of four substatements, which reason about substitution in type rules, definition and multiple-definition typing judgements, and subtyping rules.

### Soundness

The main typesafety lemma (Proposition 1) is expressed in the `safety` lemma.

### Further Details

The soundness proof of Mutable DOT is an extension to WadlerFest DOT's typesafety proof. Details can be found [here](https://github.com/amaurremi/dot-calculus/blob/master/dev/lf/doc.md).
