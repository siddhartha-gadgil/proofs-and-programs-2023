---
title: "Overview"
date: 2023-01-04T08:51:53+05:30
draft: true
marp: true
math: katex
theme: gaia

--- 
# Computer Proofs and Artificial Intelligence in Mathematics

 ChatGPT and other advances in Artificial Intelligence have become popular sensations. In parallel with this has been an enormous advance in the digitization of mathematics through Interactive Theorem Provers and their libraries. Artificial Intelligence has started entering mathematics through these and other routes.
        
In this talk, I will informally discuss advances in AI and computer proofs, and how they are likely to grow and have an impact on mathematics, in conjunction and separately.

---
From the Microsoft paper on GPT 4:

"A question that might be lingering on many readers’ mind is whether GPT-4 truly understands all these concepts, or whether it just became much better than previous models at improvising on the fly, without any real or deep understanding. We hope that after reading this paper the question should almost flip, and that one might be left wondering how much more there is to true understanding than on-the-fly improvisation. Can one reasonably say that a system that passes exams for software engineering candidates is not really intelligent? Perhaps the only real test of understanding is whether one can produce new knowledge, such as proving new mathematical theorems, a feat that currently remains out of reach for LLMs."

---

### Example Problem for GPT 4 

__Prompt:__ Within the duration of one year, a rabbit population first multiplies itself by a factor $a$ and on the last day of the year $b$ rabbits are taken by humans for adoption. Supposing that on first day of the first year there are $x$ rabbits, we know that exactly $3$ years afterwards there will be a population of $27x − 26$ rabbits. What are the values of $a$ and $b$?

---
__GPT4:__ Let's call the rabbit population after one year $y$. We know that $y=a x-b$. After two years, the population will be $a y-b=a(a x-b)-b=a^2 x-a b-b$. After three years, the population will be $a\left(a^2 x-a b-b\right)-b=a^3 x-a^2 b-a b-b$. We are given that this is equal to $27 x-26$, so we have the equation:

$$
a^3 x-a^2 b-a b-b=27 x-26
$$
We can rewrite this equation as:
$$
a^3 x-27 x=a^2 b+a b+b-26
$$

--- 

Now we can factor out an $x$ on the left side and a $b$ on the right side:
$$
x\left(a^3-27\right)=b\left(a^2+a+1-26 / b\right)
$$
We can see that $a=3$ is a solution for the left side of the equation, so we can substitute that in:
$$
x(0)=b(9+3+1-26 / b)
$$

This simplifies to: $0=13 b-26$

Solving for $b$, we find that $b=2$. So $a=3$ and $b=2$ are the values we are looking for.

---

## Minerva Example

__QUESTION:__ Assume that variance of first $n$ natural numbers is $10$ and variance of first $m$ even natural numbers is $16$. Compute $m+n$.

__MODEL ANSWER:__ Variance of first $n$ natural numbers is $\frac{n^2−1}{12}$. Variance of first $m$ even natural numbers is $\frac{2^2(m^2−1)}{12}$. So, $\frac{n^2−1}{12}=10$ and $\frac{2^2(m^2−1)}{12}=16$. Solving for $n$ and $m$, we get $n=11$ and $m=7$. So, $m+n=18$.

__PROBLEM SOURCE:__ Joint Entrance Examination Main Math 2020 exam