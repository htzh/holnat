## HOL Light Native

We have adapted [John Harrison](http://www.cl.cam.ac.uk/~jrh13/)'s [HOL Light](https://github.com/jrh13/hol-light) to
be compiled into native executables. Currently files up to ```metis.ml``` (see [```hol.ml```](https://github.com/jrh13/hol-light/blob/6a2d07bf531330c6e8afdf65431ea992a744f085/hol.ml#L130) for the order
of files) have been successfully converted.

We don't change OCaml lexing conventions so we do not need preprocessors to compile. However this means we can not have capitalized value names, nor can we have letters in operators.
We prefix all-cap value names with the letter ```v```. The composition operator is now ```-|``` instead of ```o```. See ```bin/pp.ml``` for details.

We also do not use quotation. Quoted literals have all been converted to strings and instantiated with ```parse_term``` or ```parse_type``` (unless ending with ```:```).

Due to the decoupling from ```Camlp5``` and special lexing rules, we now can run with any reasonable version of OCaml.

Instead of ```#use``` scripts, we now have modules. HOL Light modules are located inside the ```Hol``` module.

We also comply with stricter OCaml linting rules. For example, unused variables and non-exhaustive matching are all errors that we fixed.

We use ```dune``` for compiling. After ```dune build```, one can do ```dune utop``` to check out the currently proved theorems. For example:

```
utop # Hol.Theorems.vEQ_REFL;;
- : Hol.Fusion.thm = |- !x. x = x
```

It should be possible to (TODO) add quotation to ```utop``` so that we can enter quoted terms directly. However we don't envision using ```utop``` for interaction in the future. Instead
the natively compiled library can be linked into a server and a browser UI can be used for interaction. This way we can benefit from the performance gain of native compilation.

