# My hobby implementation of dependent-type system

Based on ``[A Tutorial Implementation of a Dependently Typed Lambda Calculus][tutorial]'' by A. Löh, C. McBride, and W. Swiestra.
With small extension with inferrable annotated lambda term.

## Goals

- Build an inconsistent dependently-typed programming language
- Module system based on records

## References

- A. Löh, C. McBride, and W. Swiestra: "[_A Tutorial Implementation of a Dependently Typed Lambda Calculus_][tutorial]". Fundamenta Informaticae XXI. 2001.
- J. Dunfield and N. Krishnaswami: "[_Bidirectional Typing_][bidir]". ACM Computing Surveys, Volume 54, Issue 5. 2021.
- S. Najd and S. P. Jones: "[_Trees that Grow_][ttg]". Journal of Universal Computer Science, Vol. 23, no. 1. 2021.
- B. C. Pierce: "Types and Programming Languages".
- T. Altenkrich, N. A. Danielsson, A. Löh, and N. Oury: "[_$`\Pi\Sigma`$: Dependent Types without the Sugar_][pisigma]". FLOPS 2010.
- M. Lennon-Bertrand: "[_Complete Bidirectional Typing for the Calculus of Inductive Constructions_][cic-bidir]". 2021.
- A. Rossberg: "[_1ML – Core and Modules United (F-ing First-class Modules)_][1ml]", extended version. ICFP 2015.
- A. Rossberg: "[_1ML with Special Effects: F-ing Generativity Polymorphism_][1ml-gen]". WadlerFest 2016.
- G. Betarte: "[_Type checking dependent (record) types and subtyping_][betarte]". Journal of Functional Programming, Volume 10, Issue 2. 2000.
- Z. Luo: "[_Dependent Record Types Revisited_][deprec]". MLPA 2009.
- F. Pottier and D. Rémy: "_The Essense of ML Inference_". In: "Advanced Topics in Types and Programming Languages", ed. by B. C. Pierce. (Especially: §10.8 "Rows")
- C. Omar, I. Voysey, R. Chugh, and M. A. Hammer: "[_Live Functional Programming with Typed Holes_][hazel19]". POPL 2019. Extended Version.
- Z. Pan: "[_Type Hole Inference_][holeinf]". ICFP 2020.

[tutorial]: https://www.andres-loeh.de/LambdaPi/
[bidir]: https://arxiv.org/abs/1908.05839
[ttg]: https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf
[cic-bidir]: https://arxiv.org/abs/2102.06513
[1ml]: https://people.mpi-sws.org/~rossberg/1ml/1ml-extended.pdf
[1ml-gen]: https://people.mpi-sws.org/~rossberg/1ml/1ml-effects.pdf
[betarte]: https://www.cambridge.org/core/journals/journal-of-functional-programming/article/type-checking-dependent-record-types-and-subtyping/1793E1F504A8B156B7A3EF9F17A42549
[pisigma]: https://www.andres-loeh.de/PiSigma/PiSigma.pdf
[deprec]: https://www.cs.rhul.ac.uk/home/zhaohui/DRT09.pdf
[hazel19]: https://arxiv.org/abs/1805.00155
[holeinf]: https://pper.github.io/type_hole_inference.pdf
