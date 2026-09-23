import Verso
import VersoManual
import VersoBlueprint
import CriticalRadiusFive

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The lower bound: a lattice cut" =>
%%%
tag := "chapter-lower-bound"
file := "lower-bound"
shortTitle := "Lower bound"
%%%

:::group "lower-bound"
Lower bound: below √(3+φ) every orbit is confined by a lattice cut
:::

Below $`\sqrt{3+\varphi}` every orbit is finite, with a bound that does not depend on the starting
point. Every position acts on a point as an isometry whose _pivot_ lies in the lattice
$`\mathbb{Z}[\zeta]`, and along a word the pivot performs a walk on that lattice. An integer
_level_ function changes by $`+3` or $`-2` per step, so it can cross a multiple of $`5` only
through an _active_ step whose two endpoints both lie in a small window. The lens bound confines
such steps to a window shorter than the lattice period exactly when $`r^2 < 3 + \varphi`, and the
golden rotation then supplies _cut levels_ that the walk cannot cross, on both sides and for two
independent level functions. A discreteness argument turns the resulting bands into a finite set.

:::lemma_ "lemma:normal-form" (parent := "lower-bound") (lean := "CriticalRadiusFive.mapsTo_reach_left, CriticalRadiusFive.mapsTo_reach_right")
*Normal form.* Every $`g \in G_5(r)` acts at the point $`p` as a formal isometry,

$$`g(p) = m\,(p + 1 - 2\nu) - 1,`

with $`m` a fifth root of unity and $`\nu \in \mathbb{Z}[\zeta]` the _pivot_ ($`-1 + 2\nu` is the
preimage of $`-1` under $`z \mapsto m(z + 1 - 2\nu) - 1`). Let the _window_ be
$`W_p(r) := \{\, v : |p + 1 - 2v| \le r \,\}`. The turns of {uses "def:turns"}[] act on
$`(m, \nu)` as follows: $`a^{\pm1}` acts only if the pivot $`\nu` lies in $`W_p(r)`, and then
multiplies $`m` by $`\zeta^{\mp1}` without moving $`\nu`; $`b^{\pm1}` acts only if the _dumbbell
end_ $`\nu + \overline{m}` lies in $`W_p(r)`, and then multiplies $`m` by $`\zeta^{\mp1}` and moves
the pivot to $`(\nu + \overline{m}) - \overline{m'}`, where $`m'` is the new value of $`m`. A turn
that does not act fixes the point.
:::

:::proof "lemma:normal-form"
Induct along the word, starting from the identity ($`m = 1`, $`\nu = 0`). For
$`z = m(p + 1 - 2\nu) - 1` we have $`|z + 1| = |p + 1 - 2\nu|` and, since $`m\overline{m} = 1`,
$`z - 1 = m\,(p + 1 - 2(\nu + \overline{m}))`; so $`z \in D_-` exactly when $`\nu \in W_p(r)`, and
$`z \in D_+` exactly when $`\nu + \overline{m} \in W_p(r)`. Applying $`a^{\pm1}` gives
$`\zeta^{\mp1} m\,(p + 1 - 2\nu) - 1`. Applying $`b^{\pm1}` gives
$`m'(p + 1 - 2(\nu + \overline{m})) + 1 = m'(p + 1 - 2(\nu + \overline{m} - \overline{m'})) - 1` with
$`m' = \zeta^{\mp1} m`.
:::

:::lemma_ "lemma:typed-walk" (parent := "lower-bound") (lean := "CriticalRadiusFive.orbit_subset_reach")
*The pivot performs a typed walk.* Along a word applied to $`p`, the pivot performs a walk on
$`\mathbb{Z}[\zeta]`: it adds a fifth root of unity when it leaves a pivot (to reach the dumbbell
end) and subtracts one when it returns (to the new pivot). Let $`\mathfrak{p} = (1 - \zeta)`, a prime
of norm $`5`, and let $`\operatorname{Cl}(v) \in \mathbb{Z}/5 \cong \mathbb{Z}[\zeta]/\mathfrak{p}` be
the class of $`v`. Since $`\zeta \equiv 1 \pmod{\mathfrak{p}}`, the type is the class: pivots have class
$`0` and dumbbell ends class $`1`. Consequently, let $`V \subseteq \mathbb{Z}[\zeta]` be closed under
$`+\mu_5` from class-$`0` points and under $`-\mu_5` from class-$`1` points, within the window (for
$`v \in V` and $`e \in \mu_5`: $`v + e \in V` if $`\operatorname{Cl}(v) = 0` and $`v + e \in W_p(r)`,
and $`v - e \in V` if $`\operatorname{Cl}(v) = 1` and $`v - e \in W_p(r)`), and let it contain each of
the starting pivot $`0` and dumbbell end $`1` that lies in the window, and at least one of them. Then
every point of the orbit $`G_5(r)\cdot p` is $`m(p + 1 - 2\nu) - 1` with $`m \in \mu_5` and
$`\nu \in V` or $`\nu + \overline{m} \in V`.
:::

:::proof "lemma:typed-walk"
By {uses "lemma:normal-form"}[], a turn $`a^{\pm1}` keeps the pivot, and a turn $`b^{\pm1}` passes
through the dumbbell end $`\nu + \overline{m}` (the pivot plus the fifth root of unity
$`\overline{m}`) to the new pivot $`(\nu + \overline{m}) - \overline{m'}` (the dumbbell end minus the
fifth root of unity $`\overline{m'}`). Every fifth root of unity is $`\equiv 1 \pmod{\mathfrak{p}}`, so
the class goes up by one when the walk leaves a pivot and down by one when it returns; the walk
starts at the pivot $`0`, of class $`0`, with dumbbell end $`1`. A turn acts only at a pivot or a
dumbbell end in the window, which is exactly what the closure conditions on $`V` cover.
:::

:::definition "def:level" (parent := "lower-bound") (lean := "CriticalRadiusFive.cutU, CriticalRadiusFive.psi, CriticalRadiusFive.level")
*The level.* Let $`u := 1 - \zeta + \zeta^2`, so that $`|u| = 2 - \varphi`, and for $`x \in \mathbb{C}`
let $`\psi_u(x) := 2\langle u, x\rangle = 2\operatorname{Re}(\overline{u}\,x)`. For
$`v \in \mathbb{Z}[\zeta]` the value $`\psi_u(v)` lies in $`\mathbb{Z}[\varphi]`; write
$`\psi_u(v) = A + B\varphi` with $`A, B \in \mathbb{Z}`. The _level_ of $`v` is the integer

$$`\operatorname{lv}(v) := -A - 3B.`

The rotated functional $`\zeta u` gives a second level in the same way. We write
$`\operatorname{lv}_1 := \operatorname{lv}` and $`\operatorname{lv}_2` for the level of
$`\psi_{\zeta u}`; since $`\psi_{\zeta u}(v) = \psi_u(\zeta^{-1} v)`, we have
$`\operatorname{lv}_2(v) = \operatorname{lv}_1(\zeta^{-1} v)`.
:::

:::lemma_ "lemma:step-table" (parent := "lower-bound") (lean := "CriticalRadiusFive.level_of_mem_units, CriticalRadiusFive.psi_of_level_eq_three, CriticalRadiusFive.level_emod_five")
*The step table.* For every fifth root of unity $`e`, $`\operatorname{lv}(e) \in \{3, -2\}`, and
$`\psi_u(e) = 3 - 2\varphi` whenever $`\operatorname{lv}(e) = 3`; the two roots with
$`\operatorname{lv}(e) = 3` are the _active_ directions. Moreover
$`\operatorname{lv}(v) \equiv 3\operatorname{Cl}(v) \pmod 5`, so class-$`0` points have
$`\operatorname{lv} \equiv 0` and class-$`1` points have $`\operatorname{lv} \equiv 3 \pmod 5`. The same
holds for $`\operatorname{lv}_2` and $`\psi_{\zeta u}`. Here $`\operatorname{lv}` is the level of
{uses "def:level"}[] and $`\operatorname{Cl}` the class of {bpref "lemma:typed-walk"}[].
:::

:::proof "lemma:step-table"
The functional $`\psi_u` is additive, so $`\operatorname{lv}` is additive. Direct computation gives,
for $`e = 1, \zeta, \zeta^2, \zeta^3, \zeta^4`, the values
$`\psi_u(e) = 3 - 2\varphi,\ -4 + 2\varphi,\ 3 - 2\varphi,\ -1 + \varphi,\ -1 + \varphi`, hence levels
$`3, -2, 3, -2, -2`. Both $`3` and $`-2` are $`\equiv 3 \pmod 5` and every root of unity has class
$`1`, so for $`v = \sum_j c_j \zeta^j` we get
$`\operatorname{lv}(v) \equiv 3\sum_j c_j \equiv 3\operatorname{Cl}(v) \pmod 5`. Since
$`\operatorname{lv}_2(v) = \operatorname{lv}_1(\zeta^{-1}v)` and multiplication by $`\zeta^{-1}`
permutes the fifth roots of unity and preserves classes, the same holds for $`\operatorname{lv}_2`.
:::

:::lemma_ "lemma:active-step" (parent := "lower-bound") (lean := "CriticalRadiusFive.level_mem_band, CriticalRadiusFive.level_ne_of_isCutLevel")
*Only active steps break a level bound.* Let $`q \in \mathbb{Z}`. Along the typed walk, the invariant
"$`\operatorname{lv}(v) \le 5q` for all visited $`v`" can only be destroyed by an active step
($`\operatorname{lv}(e) = 3`) leaving a class-$`0` point at level exactly $`5q`; symmetrically, the
invariant "$`\operatorname{lv}(v) > 5q` for all visited $`v`" can only be destroyed by an active step
taken backwards, arriving at a class-$`0` point at level exactly $`5q`. For such a step both endpoints
lie in the window, so the lens bound applies, with the same constant for both active directions. The
same holds for $`\operatorname{lv}_2`.
:::

:::proof "lemma:active-step"
Use the step table {uses "lemma:step-table"}[] and the typed walk {uses "lemma:typed-walk"}[]. A step
out of class $`0` adds $`e` and changes the level by $`\operatorname{lv}(e) \in \{3, -2\}`; since
$`\operatorname{lv}(v) \equiv 0 \pmod 5`, the bound $`\operatorname{lv}(v) \le 5q` survives unless
$`\operatorname{lv}(e) = 3` and $`\operatorname{lv}(v) = 5q`, while $`\operatorname{lv}(v) > 5q` forces
$`\operatorname{lv}(v) \ge 5q + 5` and survives. A step out of class $`1` subtracts $`e`; since
$`\operatorname{lv}(v) \equiv 3 \pmod 5`, the bound $`\operatorname{lv}(v) \le 5q` forces
$`\operatorname{lv}(v) \le 5q - 2` and survives, while $`\operatorname{lv}(v) > 5q` forces
$`\operatorname{lv}(v) \ge 5q + 3` and survives unless $`\operatorname{lv}(e) = 3` and
$`\operatorname{lv}(v) = 5q + 3`, in which case the step arrives at the class-$`0` point $`v - e` at
level exactly $`5q`. Both endpoints of the step are points where a turn acts, hence lie in the window.
By the step table $`\psi_u(e) = 3 - 2\varphi` for both active directions.
:::

:::lemma_ "lemma:lens-bound" (parent := "lower-bound") (lean := "CriticalRadiusFive.abs_re_mul_add_le")
*The lens bound.* Let $`U, g \in \mathbb{C}` with $`|g| = 1`, and put
$`C = |\operatorname{Re}(Ug)|`, $`D = |\operatorname{Im}(Ug)|`. If $`|w| \le r`, $`|w'| \le r` and
$`w - w' = 2g`, that is, the midpoint $`(w + w')/2` ranges over the lens of two disks of radius $`r`
at distance $`2`, then

$$`|\operatorname{Re}(U(w + w'))| \le 2D\sqrt{r^2 - 1},`

provided $`C^2(r^2 - 1) \le D^2`; under this condition the tip of the lens is the maximiser.
:::

:::proof "lemma:lens-bound"
Write $`\xi := \tfrac12(w + w')\,\overline{g} = x + iy`. Then $`w\overline{g} = \xi + 1` and
$`w'\overline{g} = \xi - 1`, so the two disk conditions give $`(|x| + 1)^2 + y^2 \le r^2`; in
particular $`r \ge 1`. Moreover
$`\operatorname{Re}(U(w + w')) = 2\operatorname{Re}(Ug\,\xi) = 2(\operatorname{Re}(Ug)\,x - \operatorname{Im}(Ug)\,y)`,
whose absolute value is at most $`2(C|x| + D|y|)`. On the region $`(|x| + 1)^2 + y^2 \le r^2` the
linear form $`C|x| + D|y|` is maximised at the tip $`x = 0`, $`|y| = \sqrt{r^2 - 1}` as soon as
$`C\sqrt{r^2 - 1} \le D`, which gives the bound $`2D\sqrt{r^2 - 1}`.
:::

:::lemma_ "lemma:window" (parent := "lower-bound") (lean := "CriticalRadiusFive.abs_psi_sub_cutCenter_le, CriticalRadiusFive.psi_add_level")
*The window of an active step.* Let $`r^2 < 3 + \varphi`, let $`\delta := 3 - \varphi` and
$`D_5 := \tfrac12\sqrt{5 - 2\sqrt5}`. If $`v` is a class-$`0` point at level $`5q` and $`v`, $`v + e`
lie in $`W_p(r)` for an active direction $`e`, then $`\psi_u(v)` lies in the window of length
$`2D_5\sqrt{r^2 - 1}` about the centre $`Z_p := \langle u, p + 1\rangle - \tfrac12(3 - 2\varphi)`,
which depends only on $`p`. On class $`0` the values at level $`5q` form a lattice of period
$`\delta` rotated by the golden number: $`\psi_u(v) = \delta P - \delta\alpha q` with
$`P \in \mathbb{Z}` and $`\alpha = 1/\varphi`. The same holds for $`\psi_{\zeta u}` and
$`\operatorname{lv}_2`.
:::

:::proof "lemma:window"
Apply {uses "lemma:lens-bound"}[] with $`U = \overline{u}`, $`g = e`, $`w = p + 1 - 2v` and
$`w' = p + 1 - 2(v + e)`, so that $`w - w' = 2e` and $`|w|, |w'| \le r`. By
{uses "lemma:step-table"}[], $`\operatorname{Re}(\overline{u}e) = \tfrac12\psi_u(e) = \tfrac12(3 - 2\varphi)`,
so $`C = \tfrac12(\sqrt5 - 2)` and $`D = \sqrt{|u|^2 - C^2} = D_5`; the side condition
$`C^2(r^2 - 1) \le D^2` holds for $`r^2 \le 6 + 2\sqrt5`, in particular for $`r^2 < 3 + \varphi`. Since
$`\operatorname{Re}(\overline{u}(w + w')) = 2\langle u, p + 1\rangle - 2\psi_u(v) - \psi_u(e) = 2(Z_p - \psi_u(v))`,
the lens bound gives $`|\psi_u(v) - Z_p| \le D_5\sqrt{r^2 - 1}`. For the lattice: writing
$`\psi_u(v) = A + B\varphi`, we have $`\psi_u(v) + \operatorname{lv}(v) = (\varphi - 3)B = -\delta B`, so at
level $`5q` (which is where class-$`0` points sit, by the step table),
$`\psi_u(v) = -\delta B - 5q = \delta P - \delta\alpha q` with $`P := -B - 3q`, because
$`\delta(3 + \alpha) = 5`.
:::

:::lemma_ "lemma:window-lt-period" (parent := "lower-bound") (lean := "CriticalRadiusFive.two_mul_lensWidth_lt")
*The window is shorter than the period.* For $`r \ge 1`,
$`2D_5\sqrt{r^2 - 1} < \delta` exactly when $`r^2 < 3 + \varphi`. This is where $`\sqrt{3+\varphi}`
enters.
:::

:::proof "lemma:window-lt-period"
Both sides are nonnegative. Squaring, $`(2D_5)^2(r^2 - 1) = (5 - 2\sqrt5)(r^2 - 1)` and
$`\delta^2 = (3 - \varphi)^2 = \tfrac12(15 - 5\sqrt5)`, and
$`\tfrac{15 - 5\sqrt5}{2(5 - 2\sqrt5)} = \tfrac{5 + \sqrt5}{2} = 2 + \varphi`. So the inequality says
$`r^2 - 1 < 2 + \varphi`.
:::

:::lemma_ "lemma:cut-levels" (parent := "lower-bound") (lean := "CriticalRadiusFive.exists_cut_levels, CriticalRadiusFive.IsCutLevel, CriticalRadiusFive.exists_isCutLevel")
*Cut levels under the golden rotation.* Let $`\delta > 0`, $`0 \le L < \delta/2`, and let
$`s \in \mathbb{R}` be irrational; in our application $`s = -\alpha` with $`\alpha = 1/\varphi`, the
golden rotation. Call $`q \in \mathbb{Z}` a _cut level_ for $`Z \in \mathbb{R}` if
$`|\delta P + \delta s q - Z| > L` for all $`P \in \mathbb{Z}`, that is, if the point
$`qs - Z/\delta` of $`\mathbb{R}/\mathbb{Z}` avoids the arc $`[-\eta, \eta]`, $`\eta = L/\delta < \tfrac12`.
There is $`N`, depending only on $`\eta` and $`s`, such that for every $`Z` there are cut levels
$`q_+ \in [1, N]` and $`q_- \in [-N, -1]`: on both sides, for $`\alpha` and for $`-\alpha` alike,
uniformly in $`Z`.
:::

:::proof "lemma:cut-levels"
Dividing by $`\delta` turns the condition into $`qs - Z/\delta \notin [-\eta, \eta] + \mathbb{Z}`.
First find a small step: an integer $`k \ge 1` for which $`ks` lies within a prescribed
$`\varepsilon > 0` of an integer, and not at an integer, since $`s` is irrational. For the golden
rotation the Fibonacci approximations $`F_{m+1}\alpha - F_m = (-1)^m\alpha^{m+1}` provide such steps;
for any irrational $`s`, Dirichlet's approximation theorem does, and this is the route of the formal
proof. Take $`\varepsilon < 1 - 2\eta` and march from the level $`1` (or $`-1`) through the multiples
of $`k`: the points move around $`\mathbb{R}/\mathbb{Z}` in steps shorter than the complementary arc,
which has length $`1 - 2\eta`, so one of a bounded number of them lands in it. The bound depends on
$`\eta` and $`s` only, not on $`Z`.
:::

:::theorem "thm:confinement" (parent := "lower-bound") (lean := "CriticalRadiusFive.edgeClosed_cutSet, CriticalRadiusFive.good_cutSet, CriticalRadiusFive.mem_box_of_mem_cutSet")
*Confinement.* Let $`0 \le r < \sqrt{3+\varphi}`. For every $`p`, the typed walk of $`p` stays in
two bands, $`5q_-^{(i)} < \operatorname{lv}_i \le 5q_+^{(i)}` for $`i = 1, 2`, between cut levels of
the two functionals $`u` and $`\zeta u`, where $`|q_\pm^{(i)}| \le N` for an $`N` depending only on
$`r`. A lattice point of $`\mathbb{Z}[\zeta]` whose physical position and conjugate coordinates
(under the Galois automorphism $`\zeta \mapsto \zeta^2`) are bounded lies in a finite set. Hence every
orbit of $`G_5(r)` lies in a finite set of at most $`N(r)` points, with $`N(r)` independent of
$`p`.
:::

:::proof "thm:confinement"
If $`p` lies outside both disks, its orbit is $`\{p\}`; otherwise $`|p| \le 1 + r`. Put
$`L = D_5\sqrt{r^2 - 1}`. By {uses "lemma:window-lt-period"}[], $`2L < \delta`, so
{uses "lemma:cut-levels"}[] (with $`s = -\alpha`) gives, for the centres $`Z_p^{(1)}, Z_p^{(2)}` of the
two functionals, cut levels $`q_+^{(i)} \in [1, N]` and $`q_-^{(i)} \in [-N, -1]`.

Let $`V` consist of the lattice points $`v` of the window, of class $`0` or $`1`, with
$`5q_-^{(i)} < \operatorname{lv}_i(v) \le 5q_+^{(i)}` for $`i = 1, 2`. Since $`p` lies in one of the
disks, the starting pivot $`0` (if $`p \in D_-`) or the starting dumbbell end $`1` (if $`p \in D_+`)
lies in the window, and their levels ($`0` and $`3` for $`\operatorname{lv}_1`, $`0` and $`-2` for
$`\operatorname{lv}_2`) lie in the bands. By {uses "lemma:active-step"}[],
a step of the walk leaving $`V` would be an active step with both endpoints in the window whose
class-$`0` endpoint $`v` sits at level exactly $`5q` for one of the four cut levels $`q`. By
{uses "lemma:window"}[], $`\psi_{u_i}(v) = \delta P - \delta\alpha q` then lies within $`L` of
$`Z_p^{(i)}`, which contradicts the choice of $`q` as a cut level. So $`V` is closed in the sense of
{bpref "lemma:typed-walk"}[], and every point of the orbit of $`p` is
$`m(p + 1 - 2\nu) - 1` with $`m \in \mu_5` and $`\nu \in V` or $`\nu + \overline{m} \in V`.

Discreteness. Every $`v \in V` has $`|v| \le 1 + r`, hence bounded values $`\psi_{u_i}(v)`, and
bounded levels $`|\operatorname{lv}_i(v)| \le 5N`. Write $`\psi_{u_i}(v) = A_i + B_i\varphi`. The
Galois conjugate $`A_i + B_i(1 - \varphi) = \varphi^2\psi_{u_i}(v) + \varphi\operatorname{lv}_i(v)` is
bounded too; it is the value at the conjugate point $`\sigma(v)` of a functional, and the two
functionals have independent directions, so $`\sigma(v)` is bounded. Since $`\mathbb{Z}[\zeta]` is
discrete in $`\mathbb{C} \times \mathbb{C}` under $`v \mapsto (v, \sigma(v))`, $`V` lies in a finite
set. Concretely, and this is how the formal proof argues: $`\psi_{u_i}(v) + \operatorname{lv}_i(v) = -\delta B_i`
bounds the integers $`B_1, \operatorname{lv}_1, B_2, \operatorname{lv}_2`, which determine $`v` through
an integer matrix of determinant $`-5`, so $`V` lies in a box of lattice points whose size depends only
on $`r`. The points $`m(p + 1 - 2\nu) - 1` with $`m \in \mu_5` and $`\nu` or $`\nu + \overline{m}` in
that box are at most $`N(r)` in number, independently of $`p`.
:::

:::theorem "thm:lower" (parent := "lower-bound") (lean := "CriticalRadiusFive.finite_GG_five_of_lt")
*The lower bound.* For every $`r < \sqrt{3+\varphi}`, $`G_5(r)` is finite; hence
$`\sqrt{3+\varphi} \le r_c(5)`.
:::

:::proof "thm:lower"
For $`r < 0` both turns are the identity. For $`0 \le r < \sqrt{3+\varphi}`,
{uses "thm:confinement"}[] bounds every orbit by $`N(r)`, and $`G_5(r)` is generated by the two
turns, so {uses "thm:T1"}[] shows that it is finite. Finally {uses "lemma:crit-lower"}[] with
$`r_0 = \sqrt{3+\varphi}` gives $`\sqrt{3+\varphi} \le r_c(5)`.
:::
