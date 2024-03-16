# Synthetic Algebraic Geometry in the Zariski-Topos
Stay updated on synthetic algebraic geometry by [watching this repository](#watching-this-repo), joining the next [meeting](https://felix-cherubini.de/sag-meeting-4.html) or with the [mailing list](https://lists.chalmers.se/mailman/listinfo/sag).
Due to a *bug* in the mailinglist-service of chalmers, it does not work to just answer to the  email-confirmation email - so use the link to confirm your email address instead. You know that you really signed up to the list, if you can login on the page linked above. 

This is a latex documentation of our understanding of the synthetic theory of the Zariski-Topos
and related ideas. The drafts below are currently built hourly -
if you want to make sure you are viewing the latest built, CTRL+F5 should clear all caches in most browsers.
There are currently the following parts:
- Foundations ([latest pdf](https://felix-cherubini.de/iag.pdf), [arxiv](https://arxiv.org/abs/2307.00073))
- Čech-Cohomology ([early draft pdf](https://felix-cherubini.de/cech.pdf))
- Differential Geometry/étale maps ([early draft pdf](https://felix-cherubini.de/diffgeo.pdf))
- Proper Schemes ([early draft pdf](https://felix-cherubini.de/proper.pdf))
- Topology of Synthetic Schemes ([early draft pdf](https://felix-cherubini.de/topology.pdf))
- $\mathbb A^1$-homotopy theory ([early draft pdf](https://felix-cherubini.de/A1-homotopy.pdf))
- Algebraic spaces and stacks ([very early draft pdf](https://felix-cherubini.de/stacks.pdf))
- Automorphisms of and line bundles on projective space ([very early draft pdf](https://felix-cherubini.de/projective.pdf))
- More general topologies, in particular fppf ([very early draft pdf](https://felix-cherubini.de/sheaves.pdf))
- Calculations with (elliptic) curves and divisors ([very early draft pdf](https://felix-cherubini.de/elliptic.pdf))
- Synthetic stone duality ([very early draft pdf](https://felix-cherubini.de/condensed.pdf))
- Finite schemes in SAG ([very early draft pdf](https://felix-cherubini.de/finite.pdf))
- Random Facts, i.e. a collection of everything that still needs to find a good place ([very early draft pdf](https://felix-cherubini.de/random.pdf))
- Collection of exercises ([pdf with exercise-ideas](https://felix-cherubini.de/exercises.pdf))

There is a related [formalization project](https://github.com/felixwellen/synthetic-geometry).


# Questions

- Is every étale proposition (formally étale and a scheme) an open proposition?
- Is every étale scheme a sub-quotient of a finite set?
- For $f : A$, is $f$ not not zero iff $f$ becomes zero in $A \otimes R/\sqrt{0}$?
  (A corollary of that would be: If the algebra $A$ is not not trivial, then it is trivial.)
- If $A$ is an étale $R$-algebra (finitely presented and the spectrum is étale),
  is it impossible to have an injective algebra map $R[X] \to A$?
- Is the proposition "X is affine" not-not-stable, for X a scheme?
  (Then deformations ($D(1) \to \mathrm{Sch}$) of affine schemes would stay affine.)
- Can every bundle (on $Sp A$) of strongly quasicoherent $R$-modules be recovered
  from its $A$-module of global sections?
- Can we compute some interesting étale/fppf cohomology groups?
- Is the intergral closure of $R$ in a finitely presented $R$-algebra $A$ finitely presented?

# Answered Questions
- Is $\mathrm{Spec} A$ quasi-complete ("compact") for $A$ a finite $R$-algebra (fin gen as $R$-module)?

  *Yes*: By the discussion in [#5](../../issues/5) and [#6](../../issues/6), $\mathrm{Spec} A$ is even projective, whenever $A$ is finitely generated as an $R$-module.
- Can there be a flat-modality for $\mathbb{A}^1$-homotopy theory?

  *No*: By the disucssion in [#18](../../issues/18), this should not be possible, because it would imply that the category of $\mathbb{A}^1$-local types is a topos, which is known to be false.
  
# Learning material
There are some [recordings](https://www.youtube.com/playlist?list=PLrnCInSNK7UT_JnKwnderE8eIkWtoW_az) of talks from the last [workshop](https://www.felix-cherubini.de/sag-meeting-3.html) on synthetic algebraic geometry.
And there is [hottest talk](https://www.youtube.com/watch?v=lp4kcmQ0ueY) on the foundations article.

# Building the drafts

We use latex now instead of xelatex, to be compatible with the arxiv.
For each draft, a build command may be found at the start of ```main.tex```.

# Arxiv

To put one of the drafts on the arxiv, we have to

- copy everything into one (temporary) folder: all tex-files, zariski.cls, zariski.sty from util and main.bbl.
- change the paths in zariski.cls and main.tex
- possibly change formulation from "This is a draft [...]"
- test by running latexmk
- put all the files into a ```.tar.gz```, so everything can be uploaded in one step

# Watching this repo
... is a good idea since we started to use the issue-tracker 

![grafik](https://github.com/felixwellen/synthetic-zariski/assets/22154668/1716ae10-4692-4549-abbf-955b2cdb8aac)


for mathematical discussions. 
If you watch this repo, you should be notified by email if there are new posts.
You can watch it, by clicking this button:

![grafik](https://github.com/felixwellen/synthetic-zariski/assets/22154668/a25ec091-f1db-42bb-9d0f-3c1dff47c8f6)

