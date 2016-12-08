# Correspondence Between Coq Proof and Mutable WadlerFest DOT Paper

## Abstract syntax

In the paper, the abstract syntax is shown in Figure 1.

In the proof, variables are represented using the inductive `avar` type, which can refer to a named or de Bruin indexed variable. The stack γ is represented using `stack`, which is a list of pairs of variables and values. The mutable store σ is represented using `store`, a map from addresses (locations) to variables. The type environment Γ is a list of pairs of variables and types `ctx`, and the store typing Σ is a list `store` of pairs of addresses and types.

Types are represented using the datatype `typ`, terms using `trm`.

## Reduction Rules

In the paper, the reduction rules are shown in Figure 5.

In the proof, the operational semantics is defined in the inductive relation `red`. 
`red γ σ t γ' σ' t'` denotes the reduction step σ|γ|t ⟼  σ'|γ'|t'.

## Type Rules

The typing and subtyping rules are depicted in Figures 4 and 5 of the paper.

In the proof, they are defined through mutually inductive definitions `ty_trm` and `subtyp`. A typing relation is characterized using two modes: 
- `tymode`, which can be `ty_precise` or `ty_general` (precise or general typing), and
- `submode`, which can be `sub_tight` or `sub_general` (tight or general subtyping).

`ty_trm m₁ m₂ Γ Σ t T` corresponds to the typing relation Γ, Σ ⊢ t: T with typing and subtyping modes m₁ and m₂.

Similarly, `subtyp m₁ m₂ Γ Σ T U` corresponds to the subtyping relation Γ, Σ ⊢ T <: U with modes m₁ and m₂.

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
