# Sum of Four Squares

This package proves two of the results in the paper [Partial Fractions and Four Classicai Theorems of Number Theory](https://doi.org/10.2307/2589321) by Michaep D. Hirschhorn: Jacobi's Sum of Two Squares formula and Jacobi's Sum of Four Squares formula. (The remaining two theorems, Dirichlet's formula and Lorenz's formula, were not proven due to time constraints.) The main theorem is `Jacobi_sum_of_four_squares`, which can be found in the file `SumOfFourSquares/Formulae.lean`. (It uses `sum_sq_sq_sq_sq`, which is located in the same file.)

Special thanks to Kenny Lau, Seewoo Lee, and Ken Ono for [their proof of the Jacobi Triple Product](https://arxiv.org/pdf/2607.01544); Seewoo Lee for [his formalization of the Jacobi Triple Product for ℂ](https://github.com/seewoo5/RogersRamanujan); to Noah Walker for answering the questions I had the process of creating this package; and to Kim Morrison for additional ideas he provided during the Lean Community Office Hours. Also, thanks to the Lean Community overall for helping me find resources while writing this formalization!

This package was not written with AI, but the two packages above were created using AI.
