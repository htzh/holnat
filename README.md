## HOL Light Native

We have adapted [John Harrison](http://www.cl.cam.ac.uk/~jrh13/)'s [HOL Light](https://github.com/jrh13/hol-light) to
be compiled into native executables.  See [```hol.ml```](https://github.com/jrh13/hol-light/blob/6a2d07bf531330c6e8afdf65431ea992a744f085/hol.ml#L166) for the files that have been successfully converted.

### Installation

We use ```dune``` for compiling. To speed up loading time we have implemented a theorem caching mechanism (see below). To enable this feature, after ```dune build```, execute ```bin/save_db.exe``` from command line. This will save a binary copy of the theorems to a file named ```db``` and makes following sessions (interactive or not) significantly faster to start.

One can do ```dune utop``` to check out the currently proved theorems. For example:
```
utop # Hol.Theorems.vEQ_REFL;;
- : Hol.Fusion.thm = |- !x. x = x
```
To use the ```help``` command one needs to copy over the [```Help/```](https://github.com/jrh13/hol-light/tree/master/Help) subfolder from [HOL Light](https://github.com/jrh13/hol-light).

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

While startup time of 1 sec is still noticeable it is significantly less painful than 10 seconds! Timings are done on an Apple M1 MacBook Air. This obviates the need for checkpointing and the cached db is only about 1.4MB.

### Difference from the original HOL Light

We don't change OCaml lexing conventions so we do not need preprocessors to compile. However this means we can not have capitalized value names, nor can we have letters in operators.
We prefix all-cap value names with the letter ```v```. The composition operator is now ```-|``` instead of ```o```. See ```bin/pp.ml``` for details.

Quoted literals can be entered using ```[q%{|``` and ```|}]```. Be sure to ```open Hol.Parser``` first as the quoted literal needs to be processed with ```parse_term``` or ```parse_type``` (unless ending with ```:```).

```
utop # open Hol.Parser;;
utop # let t = [%q{|a /\ b
                    => c|}];;
val t : Hol.Fusion.term = `a /\ b => c`
utop # let ty = [%q {|:A|} ];;
val ty : Hol.Fusion.hol_type = `:A`
```

Due to the decoupling from ```Camlp5``` and special lexing rules, we now can run with any reasonable version of OCaml.

Instead of ```#use``` scripts, we now have modules. HOL Light modules are located inside the ```Hol``` module. Note this naming convention may cause problems in utop if ```Hol.Fusion``` is opened, as it has an internal module with the same ```Hol``` name. We may change the names in the future.

We also comply with stricter OCaml linting rules. For example, unused variables and non-exhaustive matching are all errors that we fixed.

### TODOs

[x] It should be possible to add quotation so that we can enter quoted terms directly. I need to learn more about ```ppxlib``` on how this can be done. 

[ ] ```utop``` still loads bytecode so is much slower (even though caching improved the loading time here significantly as well). We don't envision using ```utop``` for interaction in the future. Instead
the natively compiled library can be linked into a server and a browser UI can be used for interaction. This way we can benefit from the performance gain of native compilation.

### Notes on caching theorems

Let's say we load modules using cached theorems and save the database again, it may be a surprise to some that the newly saved database file is obviously different from the first saved version. This transform is idempotent: if we load again with the second saved database and save again, there is no more change. It is perfectly fine to use any of the two versions.

The reason for the difference is that when we run with cached theorems (instead of reproving them) we run into significantly fewer cases of "inventing type variables": those unresolved types from parsing HOL terms. So the two different runs encode these type variables with different numbers, resulting in different databases. Moreover the theorems are structurally equal only if we unify the type variables:

```
utop # open Hol.Cache;;
utop # let l1 = read_thms "db1";;
utop # let l2 = read_thms "db2";;
utop # let t1 = List.assoc "ALL" l1;;

val t1 : Hol.Fusion.thm =
|- (ALL P [] <=> T) /\ (ALL P (CONS h t) <=> P h /\ ALL P t)

utop # let t2 = List.assoc "ALL" l2;;

val t2 : Hol.Fusion.thm =
|- (ALL P [] <=> T) /\ (ALL P (CONS h t) <=> P h /\ ALL P t)

utop # t1 = t2;;

- : bool = false

(* now we turn off pretty printing to see the details *)

utop # Hol.Basics.variables (snd (Hol.Fusion.dest_thm t1));;
- : Hol.Fusion.term list =
[Hol.Fusion.Var ("t", Hol.Fusion.Tyapp ("list", [Hol.Fusion.Tyvar "?78408"]));
 Hol.Fusion.Var ("h", Hol.Fusion.Tyvar "?78408");
 Hol.Fusion.Var ("P",
  Hol.Fusion.Tyapp ("fun",
   [Hol.Fusion.Tyvar "?78408"; Hol.Fusion.Tyapp ("bool", [])]))]

utop # Hol.Basics.variables (snd (Hol.Fusion.dest_thm t2));;
- : Hol.Fusion.term list =
[Hol.Fusion.Var ("t", Hol.Fusion.Tyapp ("list", [Hol.Fusion.Tyvar "?18157"]));
 Hol.Fusion.Var ("h", Hol.Fusion.Tyvar "?18157");
 Hol.Fusion.Var ("P",
  Hol.Fusion.Tyapp ("fun",
   [Hol.Fusion.Tyvar "?18157"; Hol.Fusion.Tyapp ("bool", [])]))]

(* now we instantiate the type variables to the same instance and try again *)
utop # let typ = Hol.Parser.parse_type "A";;
val typ : Hol.Fusion.hol_type = Hol.Fusion.Tyvar "A"

utop # Hol.Fusion.(vINST_TYPE [typ, mk_vartype "?78408"] t1 = vINST_TYPE [typ, mk_vartype "?18157"] t2);;
- : bool = true
```
