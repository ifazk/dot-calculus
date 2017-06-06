Extensions for Dependent Object Types
-------------------------------------

We are working on type-safe extensions to the Dependent Object Types (DOT) calculus as defined by Amin et al. in their [Wadlerfest](http://infoscience.epfl.ch/record/215280/files/paper_1.pdf) paper.
The paper comes with a Coq-formalized soundness proof

We developed a [simplified]((https://github.com/amaurremi/dot-calculus/blob/master/src/tight-proof), modular version of the [original](https://github.com/samuelgruetter/dot-calculus) DOT soundness proof.
Our extensions based on that simplified proof.

Our DOT extensions are:
- mutation (adding _mutable references_ to DOT)
  ([proof](https://github.com/amaurremi/dot-calculus/blob/master/src/mutation/tight/dot_top_bot_mut.v) | [technical report](https://arxiv.org/abs/1611.07610) | [documentation](https://github.com/amaurremi/dot-calculus/blob/master/src/mutation/README.md))
- expanded type paths (adding type selections on _full paths_ of the form `p.A` instead of `x.A`, where `p` is a path and `x` is a variable)
  ([proof in progress](https://github.com/amaurremi/dot-calculus/blob/master/src/paths/tight) | [description](https://github.com/amaurremi/dot-calculus/blob/master/src/paths/README.md)).
- initialization order (developing a sound initialization order)
  ([proof in progress]((https://github.com/amaurremi/dot-calculus/blob/master/src/delayed-types) | [description](https://github.com/amaurremi/dot-calculus/blob/master/src/delayed-types/README.md)

