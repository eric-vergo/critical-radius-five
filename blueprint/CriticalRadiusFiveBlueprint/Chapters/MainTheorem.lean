import Verso
import VersoManual
import VersoBlueprint
import CriticalRadiusFive

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The theorem" =>
%%%
tag := "chapter-main-theorem"
file := "main-theorem"
shortTitle := "The theorem"
%%%

:::theorem "thm:main" (lean := "CriticalRadiusFive.criticalRadius_five, CriticalRadiusFive.finite_GG_five_iff")
*The critical radius of GG₅.*

$$`r_c(5) = \sqrt{3 + \varphi} = 2.1489611417\ldots,`

a root of $`x^4 - 7x^2 + 11`. More precisely, $`G_5(r)` is finite if and only if
$`r < \sqrt{3 + \varphi}`.
:::

:::proof "thm:main"
Combine the upper bound {uses "thm:upper"}[] and the lower bound {uses "thm:lower"}[]. For the
equivalence: if $`G_5(r)` were finite for some $`r \ge \sqrt{3+\varphi}`, then $`G_5(\sqrt{3+\varphi})`
would be finite too, by {bpref "lemma:finite-mono"}[]. The formal proof uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
:::
