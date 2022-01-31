# Cursed Pangram

From a prompt on FP Discord:

> Prompt: Create a program that can check to see if an input
> (given any way you want) contains all the letters in the
> alphabet, case-insensitive. Note that the input string will
> only be ascii, but it may contain non-alphabetic letters.
> Make it cursed.

## Solution

My approach is to embed the untyped lambda calculus into Haskell using a datatype to represent LC syntax via de Bruijn indices. Is that cursed or beautiful? You be the judge.
