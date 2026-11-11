# Lean 4 ParseIt Lemmas

Specifications for [Lean 4 / ParseIt](https://github.com/fgdorais/lean4-parseit).

All specifications are Hoare triples `Triple x pre post epost` for the `Std.Do` / `vcgen`
framework. The precondition fixes the start iterator `it`. `post` describes the result and the
iterator after a successful run. `epost` describes the error on failure.
