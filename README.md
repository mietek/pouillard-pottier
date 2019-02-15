-------------------------------------------------------------------------------

This is an archival copy with minimal updates.  Please see the [original page](https://nicolaspouillard.fr/publis/pouillard-pottier-fresh-look-agda-2010/).

-------------------------------------------------------------------------------

# A fresh look at programming with names and binders (accepted to ICFP 2010)

**Nicolas Pouillard and François Pottier**

## Abstract

A wide range of computer programs, including compilers and theorem provers, manipulate data structures that involve names and binding. However, the design of programming idioms which allow performing these manipulations in a safe and natural style has, to a large extent, remained elusive. In this paper, we present a novel approach to the problem. Our proposal can be viewed either as a programming language design or as a library: in fact, it is currently implemented within Agda. It provides a safe and expressive means of programming with names and binders. It is abstract enough to support multiple concrete implementations: we present one in nominal style and one in de Bruijn style. We use logical relations to prove that ``well-typed programs do not mix names with different scope''. We exhibit an adequate encoding of Pitts-style nominal terms into our system.

- [PDF](http://nicolaspouillard.fr/publis/pouillard-pottier-fresh-look-2010.pdf)
- [PDF (extended version)](http://nicolaspouillard.fr/publis/pouillard-pottier-fresh-look-extended-2010.pdf)
- [Agda development (HTML)](http://nicolaspouillard.fr/publis/pouillard-pottier-fresh-look-agda-2010/html/NotSoFresh.html)
- [Agda development (archive)](http://nicolaspouillard.fr/publis/pouillard-pottier-fresh-look-agda-2010.tar.gz)
