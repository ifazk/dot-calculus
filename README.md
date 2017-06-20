Extensions for Dependent Object Types
-------------------------------------

We are working on type-safe extensions to the Dependent Object Types (DOT) calculus as defined by Amin et al. in their [Wadlerfest](http://infoscience.epfl.ch/record/215280/files/paper_1.pdf) paper.

We developed a [simplified](https://github.com/amaurremi/dot-calculus/tree/master/src/simple-proof), modular version of the [original](https://github.com/samuelgruetter/dot-calculus) DOT soundness proof. For details, see our [technical report](https://arxiv.org/abs/1706.03814).

Our extensions are based on that simplified proof.

Our DOT extensions are:
- mutation (adding _mutable references_ to DOT)
  ([proof](https://github.com/amaurremi/dot-calculus/tree/master/src/mutation) | [technical report](https://arxiv.org/abs/1611.07610))
- expanded type paths (adding type selections on _full paths_ of the form `p.A` instead of `x.A`, where `p` is a path and `x` is a variable)
  ([proof in progress](https://github.com/amaurremi/dot-calculus/tree/master/src/paths))
- initialization order (developing a sound _initialization order_)
  ([proof in progress](https://github.com/amaurremi/dot-calculus/tree/master/src/initialization))
