Hip - the Haskell Inductive Prover
==================================

Automatically prove properties about Haskell programs by using
induction or coinduction. The approach taken is to compile Haskell
programs to first order theories. Induction is applied on the meta
level, and proof search is carried out by automated theorem provers
for first order logic with equality.

Supported proof techniques
--------------------------

 * Fixed point induction
 * Approximation lemma
 * Structural induction
 * Structural induction with bottom
 * Definitional Equality

Installation instructions
=========================

In the main directory, run

    cabal install

Supported theorem provers
-------------------------

You will need to install at least one or more of the following theorem provers:

  * [E
    prover](http://www4.informatik.tu-muenchen.de/~schulz/E/E.html),
    recommended, precompiled binaries [here](http://www4.informatik.tu-muenchen.de/~schulz/E/Download.html)

  * [z3](http://research.microsoft.com/en-us/um/redmond/projects/z3/),
    recommended, precompiled binaries [here](http://research.microsoft.com/en-us/um/redmond/projects/z3/download.html)

  * [vampire](http://www.vprover.org/)

  * [SPASS](http://www.spass-prover.org/)

  * [prover9](http://www.cs.unm.edu/~mccune/prover9/)

  * [equinox](https://github.com/nick8325/equinox)

Running Hip
===========

Specify the file and the provers you want to use in the command line:

    hip --provers=e examples/MapIterate.hs

If you have some other theorem prover than E prover installed, check
the `--provers` flag, documented below.

If everything works well, the map-iterate property should be proved by
fixed point induction.

Entry format
============

Anything with a type signature resulting in type `Prop` will be
considered a proof attempt. Enter it similarly as a QuickCheck
property, but with `hip`:s combinators. Example:

    prop_map_iterate :: (a -> a) -> a -> Prop [a]
    prop_map_iterate f x = map f (iterate f x) =:= iterate f (f x)

The `=:=` means structural equality, and the argument to `Prop` is the
type of the equality. In other words, this is the type of `=:=`:

    (=:=) :: a -> a -> Prop [a]

Theorem and Finite Theorem
==========================

The properties you enter are universally quantified, but the domain may
differ. If you got the result `Theorem` then your property is true
when the quantifier ranges over **all** values, including partial and
infinite values. The other result `Finite Theorem` indicates that it
is only true for finite and total values.

Options and flags
=================

Quick information about available flags can be accessed anytime by the
`--help` flag to the `hip` executable.

Specifying theorem prover
-------------------------

The `--provers` flag takes a one character description for the theorem
prover:

   * **`e`**: E prover
   * **`z`**: z3
   * **`v`**: vampire 32 bit
   * **`V`**: vampire 64 bit
   * **`s`**: SPASS
   * **`x`**: equivox

You can specify many at the same time, i.e. `--provers=zevs`, which
will run z3, E prover, vampire 32-bit and SPASS, in that order, on
each problem.

Different techniques
--------------------

  * `--reprove`:

    On `examples/MapIterate.hs`, you will hopefully quite quickly get that it is
    proved by fixed point induction, but it is naturally also provable by
    the approximation lemma. To get this output, you can use the
    `--reprove` flag to reprove theorems with other techniques.

  * `--methods`:

    To this flag you can specify which methods you wish to use:

     * **`p`**: plain, only definitional equality
     * **`i`**: induction, only finite induction
     * **`s`**: structural induction, induction with bottom base case
     * **`f`**: fixed point induction
     * **`a`**: approximation lemma

    Example:

         hip --methods=p testsuite/MonadEnv.hs

Processors and parallel proving
-------------------------------

As you probably have a multi-core machine, you might just as well use
some more processor core. While theorem provers are still usually
single-core, you can run many of them in parallel. The `--processes`
or `-p` flag will let you specify this. The default is 2, but if you
have, say, 8 cores and you want to use all of them:

    hip testsuite/Nat.hs -p=8

Timeout
-------

The default timeout is one second. It can be specified with the `-t`
or `--timeout` flag:

    hip testsuite/PatternMatching.hs -t=5

Now, each theorem prover invocation will be 5 seconds long.

Consistency
-----------

Doubting the consistency of the theories that are generated? Run `hip`
with the `--consistency` flag which will let the theorem provers try
to find a contradiction without any negated properties.

Output theory
-------------

Should you wish to inspect the generated theory, you can use
`--output` and make a `proving/` directory. Then all relevant `.tptp`
files will be put there for you to view.

Hide and `seq`
--------------

Extensional equality needs to be weakened if you want to reason about
programs with `seq`, since it is then possible to distinguish
`undefined` and `const undefined`. By using either of the equivalent
flags `--seq` or `--enable-seq`, you get `seq` in scope as well as an
appropriately weakened extensional equality.

HipSpec
=======

Our sister project, HipSpec, can be found in the `hipspec` branch.

    git checkout hipspec

Authors and contact
===================

Developed by Dan Rosén, [danr at student dot gu dot se](mailto:danr-student-gu-se),

as a Master's Thesis with supervisor [Koen Claessen](http://www.cse.chalmers.se/~koen/).

