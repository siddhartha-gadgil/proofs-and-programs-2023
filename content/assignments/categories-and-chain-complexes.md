---
title: "Categories and Chain Complexes"
date: 2022-01-31T07:18:40+05:30
draft: false
---

Recall that we can associate to a partially ordered set `$(X, \leq)$` a category with objects elements of `$X$` and morphisms corresponding to pairs `$A, B\in X$` with `$A \leq B$`, with the morphism corresponding to `$(A, B)$` having domain `$A$` and codomain `$B$`.

1. Given partially ordered sets `$(X, \leq)$` and `$(Y, \leq)$`, show that there is a bijection between __order-preserving functions__ from `$X$` to `$Y$` and __functors__ from the category corresponding to `$X$` to the category corresponding to `$Y$`.

  In what follows, by a chain complexes `$(C_*, \del_*)$` we mean a sequence of _abelian groups_ `$\{C_n\}_{n\geq 0}$` for $n\geq 0$ and homomorphisms `$\{\del_n : C_n \to C_{n-1}\}_{n\geq 1}$`, such that `$\del_n\circ \del_{n+1} = 0$` for `$n\geq 0$`.

2. Let `$(C_n, \del_n)$` and `$(C'_n, \del'_n)$` be two chain complexes. Let `$\{H_n: C_n \to C'_{n+1}\}_{n\geq 0}$` be a family of homomorphisms. Define `$\varphi_n = \del'_{n + 1}\circ H_n + H_{n - 1} \circ \del_n$` for `$n\geq 1$` and `$\varphi_0 = \del'_1\circ H_0.$` Show that `$\{\varphi_n\}_{n\geq 0}$` is a chain homomorphism.
3. Let `$(C_n, \del_n)$`, `$(C'_n, \del'_n)$` and `$(C''_n, \del''_n)$` be chain complexes. Let `$\varphi, \psi: C_* \to C'_*$` and `$\varphi', \psi': C'_* \to C''_*$` be chain homomorphisms. Suppose `$\varphi$` is chain homotopic to `$\psi$` and `$\varphi'$` is chain homotopic to `$\psi'$`. Show that `$\varphi'\circ\varphi$` is chain homotopic to `$\psi'\circ\psi$`. 
4. Let `$(C_n, \del_n)$` be the chain complex with `$C_n = \Z$` for all $n\geq 0$, with boundary homomorphisms given by, for $k\geq 0$,  `$$\del_{2k + 1}:\Z\to \Z = 0, \\ \del_{2k + 2}:\Z\to \Z =\unicode{x1D7D9}_{\Z},$$` i.e., the $0$  homomorphism in odd degrees and the identity homomorphism in even (non-zero) degrees. Let $\varphi_*: C_*\to C_*$ be the chain homomorphism with
`$\varphi_0 = \unicode{x1D7D9}_{\Z}$` (the identity) and `$\varphi_n = 0$` (the zero homomorphism) for $n \geq 1$.
    - (a) Show that `$\varphi$` is chain homotopic to the identity chain homomorphism `$\unicode{x1D7D9}: C_* \to C_*$`.
    - (b) Deduce that `$(C_n, \del_n)$` is chain homotopic to the chain complex `$(C'_n, \del'_n)$` with `$C'_0 = \Z$` and `$C'_n = 0$` for all $n \geq 1$.
