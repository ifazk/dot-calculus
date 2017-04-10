# Alternative DOT Proof

## Old Possible Types Lemma

    Γ ~ s   s(x) = v   Γ ⊢ x: T
    ---------------------------
            T ∈ PT(Γ,x,v)

## New Possible Types Lemma

    Γ good   Γ(x) = T   Γ ⊢ x: U
    ----------------------------
            U ∈ PT(Γ,x,T)

## Good Types

    good ∀(x: S)T

        record T
    ----------------
      good μ(x: T)

## Good Environments

    good {}

        x # Γ
        good Γ
        good T
    --------------
    good (Γ, x: T)
