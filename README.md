# Synthetic Algebraic Geometry in the Zariski-Topos
Stay updated on synthetic algebraic geometry by [watching this repository](#watching-this-repo), joining the next [meeting](https://felix-cherubini.de/sag-meeting-4.html) or with the [mailing list](https://lists.chalmers.se/mailman/listinfo/sag).
Due to a *bug* in the mailinglist-service of chalmers, it does not work to just answer to the  email-confirmation email - so use the link to confirm your email address instead. You know that you really signed up to the list, if you can login on the page linked above. 

This is a latex documentation of our understanding of the synthetic theory of the Zariski-Topos
and related ideas. The drafts below are currently built hourly -
if you want to make sure you are viewing the latest built, CTRL+F5 should clear all caches in most browsers.
There are currently the following preprints:
- Foundations ([latest pdf](https://felix-cherubini.de/iag.pdf), [arxiv](https://arxiv.org/abs/2307.00073), [talk](https://www.youtube.com/watch?v=lp4kcmQ0ueY))
- Automorphisms of and line bundles on projective space ([latest pdf](https://felix-cherubini.de/projective.pdf), [arxiv](https://arxiv.org/abs/2405.13916), [talk](https://www.youtube.com/watch?v=SS-47RKmnVc))

And the following drafts and notes:
- Čech-Cohomology ([early draft pdf](https://felix-cherubini.de/cech.pdf))
- Differential Geometry/étale maps ([full draft pdf](https://felix-cherubini.de/diffgeo.pdf), [article draft pdf](https://felix-cherubini.de/diffgeo-V2.pdf))
- Proper Schemes ([early draft pdf](https://felix-cherubini.de/proper.pdf))
- Topology of Synthetic Schemes ([early draft pdf](https://felix-cherubini.de/topology.pdf))
- $\mathbb A^1$-homotopy theory ([early draft pdf](https://felix-cherubini.de/A1-homotopy.pdf))
- Algebraic spaces and stacks ([very early draft pdf](https://felix-cherubini.de/stacks.pdf))
- More general topologies, in particular fppf ([very early draft pdf](https://felix-cherubini.de/sheaves.pdf))
- Calculations with (elliptic) curves and divisors ([very early draft pdf](https://felix-cherubini.de/elliptic.pdf))
- Preliminaries for Serre-Duality ([very early draft pdf](https://felix-cherubini.de/serre-duality.pdf))
- Synthetic stone duality ([very early draft pdf](https://felix-cherubini.de/condensed.pdf), [summary](https://felix-cherubini.de/condensed-summary.pdf))
- Cohomology and homotopy theory in synthetic stone duality ([very early draft pdf](https://felix-cherubini.de/condensed-cohomology.pdf))
- Notes on a model for synthetic stone duality ([very early draft pdf](https://felix-cherubini.de/condensed-sheaves.pdf))
- Finite schemes in SAG ([very early draft pdf](https://felix-cherubini.de/finite.pdf))
- Random Facts, i.e. a collection of everything that still needs to find a good place ([very early draft pdf](https://felix-cherubini.de/random.pdf))
- Collection of exercises ([pdf with exercise-ideas](https://felix-cherubini.de/exercises.pdf))

There is a related [formalization project](https://github.com/felixwellen/synthetic-geometry).
[Here](CURRENT_WORK_OVERVIEW.md) is an overview of the current ongoing work in SAG and related areas.

# Questions

- Is every étale proposition (formally étale and a scheme) an open proposition?
- Is every étale scheme a sub-quotient of a finite set?
- If $A$ is an étale $R$-algebra (finitely presented and the spectrum is étale),
  is it impossible to have an injective algebra map $R[X] \to A$?
- Can every bundle (on $Sp A$) of strongly quasicoherent $R$-modules be recovered
  from its $A$-module of global sections?
- Can we compute some interesting étale/fppf cohomology groups?
- Is the intergral closure of $R$ in a finitely presented $R$-algebra $A$ finitely presented?

# Answered Questions
- Is the proposition "X is affine" not-not-stable, for X a scheme?
  (Then deformations ($D(1) \to \mathrm{Sch}$) of affine schemes would stay affine.)

  *No*: Let $X$ be an open proposition, then up to $\neg\neg$ it is $1$ or $\emptyset$, which are both affine, but we know that not all open propositions are affine.
  
- Is $\mathrm{Spec} A$ quasi-complete ("compact") for $A$ a finite $R$-algebra (fin gen as $R$-module)?

  *Yes*: By the discussion in [#5](../../issues/5) and [#6](../../issues/6), $\mathrm{Spec} A$ is even projective, whenever $A$ is finitely generated as an $R$-module.
- Can there be a flat-modality for $\mathbb{A}^1$-homotopy theory which has the same properties as the flat in real-cohesive HoTT?

  *No*: By the disucssion in [#18](../../issues/18), this should not be possible, because it would imply that the category of $\mathbb{A}^1$-local types is a topos, which is known to be false. There can still be a flat-modality with weaker properties, for example, the global section functor should generally induce such a modality.

- For $f : A$, is $f$ not not zero iff $f$ becomes zero in $A \otimes R/\sqrt{0}$?

  *No*: for $r : R$, we have $r + (r^2)$ not not zero in $R/(r^2)$, but if it were always zero in $R/(r^2,\sqrt{0})$, then we would have a nilpotent polynomial $f : R[x]$ such that $x \in f + (x^2)$, which is false.
  
# Learning material
There are some [recordings](https://www.youtube.com/playlist?list=PLrnCInSNK7UT_JnKwnderE8eIkWtoW_az) of talks from the last [workshop](https://www.felix-cherubini.de/sag-meeting-3.html) on synthetic algebraic geometry.
And there is a [hottest talk](https://www.youtube.com/watch?v=lp4kcmQ0ueY) on the foundations article.

# Building the drafts

We use latex now instead of xelatex, to be compatible with the arxiv.
For each draft, a build command may be found at the start of ```main.tex```.

# Arxiv

To put one of the drafts on the arxiv, we have to

- make sure there is a good abstract for the draft
- make a temporary folder, e.g. ```synthetic-zariski/projective/tmp``` copy all tex-files there and run
  ```
  ../../util/zar-rebase.sh ../../util/
  ```
- run ```latexmk -pdf -pvc main.tex``` to produce the ```main.bbl``` and check if the draft builds. 
- put all the files into a ```.tar.gz```, so everything can be uploaded in one step, e.g.
  ```
  tar -czv -f DRAFT.tar.gz *.tex *.cls *.sty main.bbl
  ```
# Watching this repo
... is a good idea since we started to use the issue-tracker 

![grafik](https://github.com/felixwellen/synthetic-zariski/assets/22154668/1716ae10-4692-4549-abbf-955b2cdb8aac)


for mathematical discussions. 
If you watch this repo, you should be notified by email if there are new posts.
You can watch it, by clicking this button:

![grafik](https://github.com/felixwellen/synthetic-zariski/assets/22154668/a25ec091-f1db-42bb-9d0f-3c1dff47c8f6)

