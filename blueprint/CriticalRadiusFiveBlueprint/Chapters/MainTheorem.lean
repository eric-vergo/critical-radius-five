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

:::theorem "thm:main" (lean := "CriticalRadiusFive.criticalRadius_five, CriticalRadiusFive.finite_GG_five_iff") (uses := "def:group, def:criticalRadius")
*The critical radius of GG₅.*

$$`r_c(5) = \sqrt{3 + \varphi} = 2.1489611417\ldots,`

a root of $`x^4 - 7x^2 + 11`. More precisely, $`\mathrm{GG}_5(r)` is finite if and only if
$`r < \sqrt{3 + \varphi}`.
:::

:::proof "thm:main"
By {uses "thm:upper"}[] and {uses "thm:lower"}[], {uses "lemma:threshold"}[] applies with
$`R = \sqrt{3+\varphi}`. The formal proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
:::
