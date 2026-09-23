import Verso
import VersoManual
import VersoBlueprint
import CriticalRadiusFive

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The upper bound: three words and an irrational rotation" =>
%%%
tag := "chapter-upper-bound"
file := "upper-bound"
shortTitle := "Upper bound"
%%%

:::group "upper-bound"
Upper bound: at r = √(3+φ) three words realise an irrational rotation
:::

In this chapter $`r = \sqrt{3+\varphi}`. The group jumbles at this radius because three explicit
words act on a chord through the origin as an exchange of three intervals, which in a suitable
coordinate is the rotation of a circle by an irrational fraction of a turn. This is Theorem 2 of
Hearn, Kretschmer, Rokicki, Streeter and Vergo.

:::definition "def:points" (parent := "upper-bound") (lean := "CriticalRadiusFive.chordE, CriticalRadiusFive.smul_chordE")
*The chord E′E.* Let $`r^2 = 3 + \varphi = 4 + \varphi^{-1}` and $`E := \zeta - \zeta^2`, so that
$`|E + 1| = r`: the point $`E` lies on the boundary circle of $`D_-` and inside $`D_+`, and by
symmetry $`E' := -E` lies on the boundary circle of $`D_+` and inside $`D_-`. Hence the chord from
$`E'` to $`E`, which passes through the origin, lies in the lens $`D_- \cap D_+`. Put
$`F := \varphi^{-1} E` and $`G := 2F - E`; primes denote negatives, $`F' = -F`, $`G' = -G`. In the
coordinate $`z = sE` the points $`E', F', G', E` sit at
$`s = -1,\ -\varphi^{-1},\ 1 - 2\varphi^{-1},\ 1`.
:::

:::lemma_ "lemma:convex-words" (parent := "upper-bound") (lean := "CriticalRadiusFive.admissible_of_mem_segment, CriticalRadiusFive.wordPerm_apply_of_admissible")
*Words act on segments through their endpoints.* Let a word in the turns be applied to a segment.
If, at every letter, both endpoints of the current image segment lie in the closed disk of that
letter, then the word acts on the whole segment as the corresponding composition of rotations; in
particular it maps the segment affinely onto the segment joining the images of its endpoints.
:::

:::proof "lemma:convex-words"
Closed disks are convex: if both endpoints of a segment lie in the disk of a letter, so does the
whole segment, and the letter acts on all of it as its rotation. A rotation maps a segment onto the
segment between the images of its endpoints, so the next image is again a segment, determined by
its endpoints. Induct along the word.
:::

:::lemma_ "lemma:words" (parent := "upper-bound") (lean := "CriticalRadiusFive.piece₁, CriticalRadiusFive.piece₂, CriticalRadiusFive.piece₃")
*Three words translate the three pieces.* At $`r = \sqrt{3+\varphi}`, write $`A = a^{-1}` and
$`B = b^{-1}` for the inverse turns of {uses "def:turns"}[]. On the chord $`E'E` of
{uses "def:points"}[], the three words (read left to right)

* $`A\,A\,B\,A\,B` translates $`[E', F']` by $`+2F`,
* $`a\,b\,a\,b\,b` translates $`[F', G']` by $`+2F`,
* $`a\,b\,a\,B\,A\,B` translates $`[G', E]` by $`2F - 2E`.
:::

:::proof "lemma:words"
By {uses "lemma:convex-words"}[], a word acts on a segment as the composition of the rotations of
its letters as soon as, at every letter, both endpoints of the current image segment lie in that
letter's disk. So it suffices to follow the two endpoints of each piece through its word. They are
explicit elements of $`\mathbb{Z}[\zeta]`, and each membership test $`|w \pm 1|^2 \le r^2` is an
exact comparison in $`\mathbb{Z}[\varphi]`. The composition of the rotations is then computed to be
the stated translation.
:::

:::lemma_ "lemma:rotation" (parent := "upper-bound") (lean := "CriticalRadiusFive.chordRot, CriticalRadiusFive.exists_mem_GG_apply_smul_chordE")
*The exchange is a circle rotation.* In the coordinate $`z = sE`, $`t = s + 1 \in [0, 2)`, the three
translations of {uses "lemma:words"}[] together act as the rotation

$$`\operatorname{rot}(t) = \begin{cases} t + \alpha & (t < \beta), \\ t - \beta & (t \ge \beta) \end{cases}`

of the circle $`\mathbb{R}/2\mathbb{Z}`, with $`\alpha = 2\varphi^{-1}` and
$`\beta = 2 - 2\varphi^{-1}`, so $`\alpha + \beta = 2`.
:::

:::theorem "thm:engine" (parent := "upper-bound") (lean := "CriticalRadiusFive.orbit_infinite_of_irrational_rotation, CriticalRadiusFive.infinite_of_orbit_infinite")
*An irrational rotation makes the group infinite.* Let $`\alpha, \beta \ge 0` with $`\alpha + \beta > 0`
and $`\alpha/(\alpha+\beta) \notin \mathbb{Q}`, let $`x : [0, \alpha+\beta) \to \mathbb{C}` be
injective, and let $`G \le \operatorname{Perm}(\mathbb{C})` contain, for every
$`t \in [0, \alpha+\beta)`, an element carrying $`x(t)` to $`x(\operatorname{rot} t)`. Then for every
$`t_0` the orbit of $`x(t_0)` under $`G` is infinite; in particular $`G` is infinite.
:::

:::proof "thm:engine"
The iterates of $`t_0` under $`\operatorname{rot}` are $`t_0 + k\alpha - m_k(\alpha+\beta)` with
integers $`m_k`; they are pairwise distinct because $`\alpha/(\alpha+\beta)` is irrational. Since
$`x` is injective, the points $`x(\operatorname{rot}^k t_0)` are pairwise distinct, and they all lie
in the orbit of $`x(t_0)`, being reached by products of the given elements.
:::

:::theorem "thm:upper" (parent := "upper-bound") (lean := "CriticalRadiusFive.orbit_zero_infinite, CriticalRadiusFive.infinite_GG_five")
*The upper bound.* $`G_5(\sqrt{3+\varphi})` is infinite; hence $`r_c(5) \le \sqrt{3+\varphi}`.
:::

:::proof "thm:upper"
By {uses "lemma:rotation"}[], the words of the previous lemmas realise, on the chord $`E'E`, the
rotation by $`\alpha = 2\varphi^{-1}` of a circle of length $`\alpha + \beta = 2`, with
$`x(t) = (t-1)E` injective. The rotation number $`\alpha/(\alpha+\beta) = \varphi^{-1}` is
irrational, so by {uses "thm:engine"}[] the orbit of the origin ($`t = 1`) is infinite and
$`G_5(\sqrt{3+\varphi})` is infinite. Then {uses "lemma:crit-upper"}[] gives
$`r_c(5) \le \sqrt{3+\varphi}`.
:::
