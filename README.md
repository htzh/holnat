## HOL Light Native

We have adapted [John Harrison](http://www.cl.cam.ac.uk/~jrh13/)'s [HOL Light](https://github.com/jrh13/hol-light) to
be compiled into native executables.  See [```hol.ml```](https://github.com/jrh13/hol-light/blob/6a2d07bf531330c6e8afdf65431ea992a744f085/hol.ml#L166) for the files that have been successfully converted.

### Installation

We use ```dune``` for compiling. To speed up loading time we have implemented a theorem caching mechanism (see below). To enable this feature, after ```dune build```, execute ```bin/save_db.exe``` from command line. This will save a binary copy of the theorems to a file named ```db``` and makes following sessions (interactive or not) significantly faster to start.

One can do ```dune utop``` to check out the currently proved theorems. For example:
```
utop # vEQ_REFL;;
- : thm = |- !x. x = x
```
To use the ```help``` command one needs to copy over the [```Help/```](https://github.com/jrh13/hol-light/tree/master/Help) subfolder from [HOL Light](https://github.com/jrh13/hol-light).

### Performance of native vs byte code

We ran timing tests on ```Complex/grobner_examples.ml```. We generally see 5-6x in performance improvement when compiled with standard switches. The timing numbers are available under the [timings/](https://github.com/htzh/holnat/tree/master/timings) subfolder. The most time consuming example is for ```SHUR```, where we have 2.12s for native and 13.49s for ```utop```. Note the native version does not pretty print the theorems so the best way to see is through ```diff```:

```
1d0
< utop # Toploop.use_file Format.std_formatter "Library/Complex/grobner_examples.ml";;
...

1069,1146c796
< CPU time (user): 13.494951
< val vSCHUR : thm =
<   |- Cx (&22680) * (x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 5 =
<      Cx (&9) *
<      ((Cx (&2) * x1) pow 10 +
<       (Cx (&2) * x2) pow 10 +
<       (Cx (&2) * x3) pow 10 +
<       (Cx (&2) * x4) pow 10) +
<      Cx (&180) *
<      ((x1 + x2) pow 10 +
<       (x1 - x2) pow 10 +
<       (x1 + x3) pow 10 +
<       (x1 - x3) pow 10 +
<       (x1 + x4) pow 10 +
<       (x1 - x4) pow 10 +
<       (x2 + x3) pow 10 +
<       (x2 - x3) pow 10 +
<       (x2 + x4) pow 10 +
<       (x2 - x4) pow 10 +
<       (x3 + x4) pow 10 +
<       (x3 - x4) pow 10) +
<      ((Cx (&2) * x1 + x2 + x3) pow 10 +
<       (Cx (&2) * x1 + x2 - x3) pow 10 +
...
---
> CPU time (user): 2.115252
```

We also gave the "hideously slow" Simson's theorems a try, in native mode (we did not bother with the byte code version). The first one came in at just under 85s. The second one ran up to ```801 basis elements and 174174 critical pairs``` after close to an hour, at which point it caused a seg fault. There is a known OCaml bug for ARM64 where stack overflow is not detected. We may give this another go in the future when the bug fix is released in OCaml 13.x. The numbers for some "barely feasible" proofs in ```quelim_examples.ml``` can be found in [```quelim_examples_native.txt```](https://github.com/htzh/holnat/blob/master/timings/quelim_examples_native.txt). The last example, which now takes 236s, was considered to "take[s] too long ... and too much memory too".

Timings are done on an Apple M1 MacBook Air.

### Performance and theorem caching

Theorems don't need to be proved over and over again. We implemented a cache lookup mechanism for theorems contained in ```database.ml```. For natively compiled executables loading all the modules in ```hol``` takes a little over one second with this optimization:

```
holnat % time bin/query.exe
Number of theorems in database: 2916
Number of theorems in cache: 2916
bin/query.exe  1.22s user 0.03s system 97% cpu 1.273 total
```

Without the cached database it takes 8 times as long:
```
bin % time ./query.exe
Number of theorems in database: 2916
Number of theorems in cache: 0
./query.exe  9.95s user 0.03s system 99% cpu 9.979 total
```

While startup time of 1 sec is still noticeable it is significantly less painful than 10 seconds! This obviates the need for checkpointing and the cached db is only about 1.4MB.

### Difference from the original HOL Light

We don't change OCaml lexing conventions so we do not need preprocessors to compile. However this means we can not have capitalized value names, nor can we have letters in operators.
We prefix all-cap value names with the letter ```v```. The composition operator is now ```-|``` instead of ```o```. See ```bin/pp.ml``` for details.

Due to the decoupling from ```Camlp5``` and special lexing rules, we now can run with any reasonable version of OCaml.

Quotation is supported through ```ppxlib```. Currently it is not used in ```hol/*``` source code. ```dune utop``` enables it by default. One can also choose to use it by specifying preprocessing options in dune for executables.

Instead of ```#use``` scripts, we now have modules. HOL Light modules are located inside the ```Hol``` library module. One can ```open Hol.All``` to simulate the environment from loading the ```hol.ml``` script. This and ```#install_printer``` directives are now kept in ```.ocamlinit``` for interactive sessions. We have renamed the ```Hol``` module inside ```fusion.ml``` to ```Hol_kernel``` to both match its signature and avoid name collision if ```Hol.Fusion``` is opened.

We also comply with stricter OCaml linting rules. For example, unused variables and non-exhaustive matching are all errors that we fixed.

### Module loading order

HOL Light allows for overloading, which means the type of an HOL term like ````a+b```` is determined by preference for the type of the operator ```(+)``` at the time of parsing. The overloading interface can be changed on the fly. This introduces an ordering constraint among modules, since often modules don't completely specify the overloading interface the parser should be using, instead relying on the state of the interface it is left in by some other modules. If modules load in the wrong order terms could be parsed incorrectly.

Module loading order is determined at link time. The build system ```dune``` uses ```ocamldep``` to determine the dependency among modules. This dependency is only for definitions (values must be defined before usage) and does not reflect dependency created through mutations. To simulate the order created through ```#use``` in the proof scripts one can use ```include``` for modules. This tends to reduce the utility of module namespace isolation but is the conservative thing to do if one is not clear about the state of the overloading interface.

### Quotation

Quoted literals can be entered using PPX extension ```[%q``` and ```]```. If the string literal contains characters that need to be escaped one could use OCaml's ```{|``` ```|}``` as quotation marks instead of manually escaping them. Be sure to ```open Hol.Parser``` first as the quoted literal needs to be processed with ```parse_term``` or ```parse_type``` (unless ending with ```:```).

```
utop # let t = [%q{|a /\ b
                    ==> c|}];;
val t : term = `a /\ b ==> c`

utop # let ty = [%q ":A" ];;
val ty : hol_type = `:A`
```

To use quotation in modules, make sure ```dune``` has ```(preprocess (pps quotation))``` specified. See ```quotation/``` for an example.

For OCaml 4.11.0 and above, the shorthand form ```{%q|``` ```|}``` can be used instead.

### TODOs

[x] It should be possible to add quotation so that we can enter quoted terms directly. I need to learn more about ```ppxlib``` on how this can be done. 

[ ] ```utop``` still loads bytecode so is much slower (even though caching improved the loading time here significantly as well). We don't envision using ```utop``` for interaction in the future. Instead
the natively compiled library can be linked into a server and a browser UI can be used for interaction. This way we can benefit from the performance gain of native compilation.

### Notes on caching theorems

Let's say we load modules using cached theorems and save the database again, it may be a surprise to some that the newly saved database file is obviously different from the first saved version. This transform is idempotent: if we load again with the second saved database and save again, there is no more change. It is perfectly fine to use any of the two versions.

The reason for the difference is that when we run with cached theorems (instead of reproving them) we run into significantly fewer cases of "inventing type variables": those unresolved types from parsing HOL terms. So the two different runs encode these type variables with different numbers, resulting in different databases. Moreover the theorems are structurally equal only if we unify the type variables:

```
(* assume we only did save_db once so that "db" contains the original form of theorems *)

utop # open Hol.Cache;;
utop # let l1 = read_thms "db";;
utop # let l2 = !theorems;;
utop # let t1 = List.assoc "ALL" l1;;

val t1 : thm = |- (ALL P [] <=> T) /\ (ALL P (CONS h t) <=> P h /\ ALL P t)

utop # let t2 = List.assoc "ALL" l2;;

val t2 : thm = |- (ALL P [] <=> T) /\ (ALL P (CONS h t) <=> P h /\ ALL P t)

utop # t1 = t2;;

- : bool = false

(* now we turn off pretty printing to see the details *)

utop # variables (concl t1);;
- : term list =
[Hol.Fusion.Var ("t", Hol.Fusion.Tyapp ("list", [Hol.Fusion.Tyvar "?78408"]));
 Hol.Fusion.Var ("h", Hol.Fusion.Tyvar "?78408");
 Hol.Fusion.Var ("P",
  Hol.Fusion.Tyapp ("fun",
   [Hol.Fusion.Tyvar "?78408"; Hol.Fusion.Tyapp ("bool", [])]))]

utop # variables (concl t2);;
- : term list =
[Hol.Fusion.Var ("t", Hol.Fusion.Tyapp ("list", [Hol.Fusion.Tyvar "?18157"]));
 Hol.Fusion.Var ("h", Hol.Fusion.Tyvar "?18157");
 Hol.Fusion.Var ("P",
  Hol.Fusion.Tyapp ("fun",
   [Hol.Fusion.Tyvar "?18157"; Hol.Fusion.Tyapp ("bool", [])]))]

(* now we instantiate the type variables to the same instance and try again *)

utop # let typ = parse_type "A";;
val typ : hol_type = Hol.Fusion.Tyvar "A"

utop # (vINST_TYPE [typ, mk_vartype "?78408"] t1 = vINST_TYPE [typ, mk_vartype "?18157"] t2);;
- : bool = true
```
