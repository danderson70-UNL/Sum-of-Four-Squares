# Sum of Four Squares

This package proves two of the results in the paper [Partial Fractions and Four Classicai Theorems of Number Theory](https://doi.org/10.2307/2589321) by Michaep D. Hirschhorn. This package follows the proof given in the paper to show Jacobi's Sum of Two Squares formula and Jacobi's Sum of Four Squares formula. (If desired, I could additionally prove Dirichlet's formula and Lorenz's formula.)

Special thanks to Seewoo Lee for his formalization of the Jacobi Triple Product for $$\mathbb{C}$$, to Noah Walker for help with some issues, and to Kim Morrison for some additional ideas he provided during the Lean Community Office Hours. Also, thanks to the Lean Community overall for helping me find resources while writing this formalization!

The main theorem is `Jacobi_sum_of_four_squares`, which can be found in the file `SumOfFourSquares/Formulae.lean`. (It uses the definition of `sum_sq_sq_sq_sq`, which is located in the same file.)
