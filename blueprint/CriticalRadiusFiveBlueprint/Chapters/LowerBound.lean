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
Lower bound
:::

Below $`\sqrt{3+\varphi}` every orbit is finite, with a bound that does not depend on the starting
point. Every position acts on a point as an isometry whose _pivot_ lies in the lattice
$`\mathbb{Z}[\zeta]`, and along a word the pivot and its _tip_ perform a walk on that lattice; a turn
about one of them is possible only while it lies in a _window_ around the point. An integer _level_
function changes by $`+3` or $`-2` per step from a pivot and by $`-3` or $`+2` per step from a tip,
so a step between two points of the window can pass a multiple of $`5` only if it is an _active_
step. The lens bound confines the functional at such steps to an interval shorter than the lattice
period as long as $`r^2 < 3 + \varphi`, and the golden rotation then supplies _cut levels_ that the
walk cannot cross inside the window, on both sides and for two independent level functions. A
discreteness argument turns the resulting bands into a finite set.

:::lemma_ "lemma:normal-form" (parent := "lower-bound") (lean := "CriticalRadiusFive.mapsTo_reach_left, CriticalRadiusFive.mapsTo_reach_right") (uses := "def:group")
*Normal form.* Every $`g \in \mathrm{GG}_5(r)` acts at the point $`p` as a formal isometry,

$$`g(p) = m\,(p + 1 - 2\nu) - 1,`

with $`m` a fifth root of unity and $`\nu \in \mathbb{Z}[\zeta]` the _pivot_ ($`-1 + 2\nu` is the
preimage of $`-1` under $`z \mapsto m(z + 1 - 2\nu) - 1`). Let the _window_ be
$`W_p(r) := \{\, v : |p + 1 - 2v| \le r \,\}`. The turns of {uses "def:turns"}[] act on
$`(m, \nu)` as follows: $`a^{\pm1}` acts only if the pivot $`\nu` lies in $`W_p(r)`, and then
multiplies $`m` by $`\zeta^{\mp1}` without moving $`\nu`; $`b^{\pm1}` acts only if the _tip_
$`\nu + \overline{m}` lies in $`W_p(r)`, and then multiplies $`m` by $`\zeta^{\mp1}` and moves the
pivot to $`(\nu + \overline{m}) - \overline{m'}`, where $`m'` is the new value of $`m`. A turn that
does not act fixes the point.
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
$`\mathbb{Z}[\zeta]`: it adds a fifth root of unity when it leaves a pivot (to reach the tip) and
subtracts one when it returns (to the new pivot). Let $`\mathfrak{p} = (1 - \zeta)`, a prime of norm
$`5`, and let $`\operatorname{cl}(v) \in \mathbb{Z}/5 \cong \mathbb{Z}[\zeta]/\mathfrak{p}` be the
class of $`v`. Since $`\zeta \equiv 1 \pmod{\mathfrak{p}}`, the type is the class: pivots have class
$`0` and tips class $`1`. Consequently, let $`V \subseteq \mathbb{Z}[\zeta]` be closed under
$`+\mu_5` from class-$`0` points and under $`-\mu_5` from class-$`1` points, within the window (for
$`v \in V` and $`e \in \mu_5`: $`v + e \in V` if $`\operatorname{cl}(v) = 0` and
$`v + e \in W_p(r)`, and $`v - e \in V` if $`\operatorname{cl}(v) = 1` and $`v - e \in W_p(r)`), and
let it contain each of the starting pivot $`0` and tip $`1` that lies in the window, and at least
one of them. Then every point of the orbit $`\mathrm{GG}_5(r)\cdot p` is $`m(p + 1 - 2\nu) - 1` with
$`m \in \mu_5` and $`\nu \in V` or $`\nu + \overline{m} \in V`.
:::

:::proof "lemma:typed-walk"
By {uses "lemma:normal-form"}[], a turn $`a^{\pm1}` keeps the pivot, and a turn $`b^{\pm1}` passes
through the tip $`\nu + \overline{m}` (the pivot plus the fifth root of unity $`\overline{m}`) to the
new pivot $`(\nu + \overline{m}) - \overline{m'}` (the tip minus the fifth root of unity
$`\overline{m'}`). Every fifth root of unity is $`\equiv 1 \pmod{\mathfrak{p}}`, so the class goes
up by one when the walk leaves a pivot and down by one when it returns; the walk starts at the pivot
$`0`, of class $`0`, with tip $`1`. A turn acts only at a pivot or a tip in the window, which is
exactly what the closure conditions on $`V` cover.
:::

:::definition "def:level" (parent := "lower-bound") (lean := "CriticalRadiusFive.cutU, CriticalRadiusFive.psi, CriticalRadiusFive.level")
*The level.* Let $`u := 1 - \zeta + \zeta^2`, so that $`|u| = 2 - \varphi`, and for $`x \in \mathbb{C}`
let $`\psi_u(x) := 2\langle u, x\rangle = 2\operatorname{Re}(\overline{u}\,x)`. For
$`v \in \mathbb{Z}[\zeta]` the value $`\psi_u(v)` lies in $`\mathbb{Z}[\varphi]`; write
$`\psi_u(v) = A + B\varphi` with $`A, B \in \mathbb{Z}`. The _level_ of $`v` is the integer

$$`\ell(v) := -A - 3B.`

The rotated vector $`\zeta u` gives a second functional $`\psi_{\zeta u}` and a second level
$`\ell_2` in the same way; since $`\psi_{\zeta u}(v) = \psi_u(\zeta^{-1} v)`, we have
$`\ell_2(v) = \ell(\zeta^{-1} v)`.
:::

:::lemma_ "lemma:step-table" (parent := "lower-bound") (lean := "CriticalRadiusFive.level_of_mem_units, CriticalRadiusFive.psi_of_level_eq_three, CriticalRadiusFive.level_emod_five")
*The step table.* For every fifth root of unity $`e`, $`\ell(e) \in \{3, -2\}`, and
$`\psi_u(e) = 3 - 2\varphi` whenever $`\ell(e) = 3`; the two roots with $`\ell(e) = 3` are the
_active_ directions. Moreover $`\ell(v) \equiv 3\operatorname{cl}(v) \pmod 5`, so class-$`0` points
have $`\ell \equiv 0` and class-$`1` points have $`\ell \equiv 3 \pmod 5`. The same holds for
$`\ell_2` and $`\psi_{\zeta u}`. Here $`\ell` is the level of {uses "def:level"}[] and
$`\operatorname{cl}` the class of {bpref "lemma:typed-walk"}[].
:::

:::proof "lemma:step-table"
The functional $`\psi_u` is additive, so $`\ell` is additive. Direct computation gives, for
$`e = 1, \zeta, \zeta^2, \zeta^3, \zeta^4`, the values
$`\psi_u(e) = 3 - 2\varphi,\ -4 + 2\varphi,\ 3 - 2\varphi,\ -1 + \varphi,\ -1 + \varphi`, hence levels
$`3, -2, 3, -2, -2`. Both $`3` and $`-2` are $`\equiv 3 \pmod 5` and every root of unity has class
$`1`, so for $`v = \sum_j c_j \zeta^j` we get
$`\ell(v) \equiv 3\sum_j c_j \equiv 3\operatorname{cl}(v) \pmod 5`. Since
$`\ell_2(v) = \ell(\zeta^{-1}v)` and multiplication by $`\zeta^{-1}` permutes the fifth roots of
unity and preserves classes, the same holds for $`\ell_2`.
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
*The window of an active step.* Let $`r^2 < 3 + \varphi`, let $`\delta := 3 - \varphi`,
$`D_5 := \tfrac12\sqrt{5 - 2\sqrt5}` and $`L(r) := D_5\sqrt{r^2 - 1}` (with $`L(r) := 0` for
$`r < 1`). If $`v` and $`v + e` lie in $`W_p(r)` for an active direction $`e`, then $`\psi_u(v)`
lies within $`L(r)` of the centre $`Z_p := \langle u, p + 1\rangle - \tfrac12(3 - 2\varphi)`, which
depends only on $`p`. At level $`5q` the values of $`\psi_u` form a progression of period
$`\delta` rotated by the golden number: $`\psi_u(v) = \delta P - \delta\alpha q` with
$`P \in \mathbb{Z}` and $`\alpha = 1/\varphi`. The same holds for $`\psi_{\zeta u}` and $`\ell_2`,
with the centre $`Z'_p := \langle \zeta u, p + 1\rangle - \tfrac12(3 - 2\varphi)`.
:::

:::proof "lemma:window"
Apply {uses "lemma:lens-bound"}[] with $`U = \overline{u}`, $`g = e`, $`w = p + 1 - 2v` and
$`w' = p + 1 - 2(v + e)`, so that $`w - w' = 2e` and $`|w|, |w'| \le r`. By
{uses "lemma:step-table"}[], $`\operatorname{Re}(\overline{u}e) = \tfrac12\psi_u(e) = \tfrac12(3 - 2\varphi)`,
so $`C = \tfrac12(\sqrt5 - 2)` and $`D = \sqrt{|u|^2 - C^2} = D_5`; the side condition
$`C^2(r^2 - 1) \le D^2` holds for $`r^2 \le 6 + 2\sqrt5`, in particular for $`r^2 < 3 + \varphi`. Since
$`\operatorname{Re}(\overline{u}(w + w')) = 2\langle u, p + 1\rangle - 2\psi_u(v) - \psi_u(e) = 2(Z_p - \psi_u(v))`,
the lens bound gives $`|\psi_u(v) - Z_p| \le D_5\sqrt{r^2 - 1} = L(r)`. For the progression: writing
$`\psi_u(v) = A + B\varphi`, we have $`\psi_u(v) + \ell(v) = (\varphi - 3)B = -\delta B`, so at level
$`5q`, $`\psi_u(v) = -\delta B - 5q = \delta P - \delta\alpha q` with $`P := -B - 3q`, because
$`\delta(3 + \alpha) = 5`.
:::

:::lemma_ "lemma:window-lt-period" (parent := "lower-bound") (lean := "CriticalRadiusFive.two_mul_lensWidth_lt")
*The window is shorter than the period.* If $`r^2 < 3 + \varphi`, then $`2L(r) < \delta`, with
$`L(r)` and $`\delta` as in {bpref "lemma:window"}[] (and, for $`r \ge 1`, only then). This is where
$`\sqrt{3+\varphi}` enters.
:::

:::proof "lemma:window-lt-period"
For $`r < 1` there is nothing to prove. For $`r \ge 1` both sides are nonnegative. Squaring,
$`(2L(r))^2 = (5 - 2\sqrt5)(r^2 - 1)` and $`\delta^2 = (3 - \varphi)^2 = \tfrac12(15 - 5\sqrt5)`, and
$`\tfrac{15 - 5\sqrt5}{2(5 - 2\sqrt5)} = \tfrac{5 + \sqrt5}{2} = 2 + \varphi`. So the inequality says
$`r^2 - 1 < 2 + \varphi`.
:::

:::lemma_ "lemma:cut-levels" (parent := "lower-bound") (lean := "CriticalRadiusFive.exists_cut_levels")
*Cut levels under the golden rotation.* Let $`\delta > 0`, $`0 \le L < \delta/2`, and let
$`s \in \mathbb{R}` be irrational; in our application $`s = -\alpha` with $`\alpha = 1/\varphi`, the
golden rotation. Call $`q \in \mathbb{Z}` a _cut level_ for $`Z \in \mathbb{R}` if
$`|\delta P + \delta s q - Z| > L` for all $`P \in \mathbb{Z}`, that is, if the point
$`qs - Z/\delta` of $`\mathbb{R}/\mathbb{Z}` avoids the arc $`[-\eta, \eta]`, $`\eta = L/\delta < \tfrac12`.
There is $`N`, depending only on $`\eta` and $`s`, such that for every $`Z` there are cut levels
$`q_+ \in [1, N]` and $`q_- \in [-N, -1]`: on both sides of $`0`, uniformly in $`Z`.
:::

:::proof "lemma:cut-levels"
Dividing by $`\delta` turns the condition into $`qs - Z/\delta \notin [-\eta, \eta] + \mathbb{Z}`.
First find a small step: an integer $`k \ge 1` for which $`ks` lies within a prescribed
$`\varepsilon > 0` of an integer, and not at an integer, since $`s` is irrational. For the golden
rotation the Fibonacci approximations $`F_{m+1}\alpha - F_m = (-1)^m\alpha^{m+1}` provide such steps;
for any irrational $`s`, Dirichlet's approximation theorem does, and this is the route of the formal
proof. Take $`\varepsilon < 1 - 2\eta` and march from the level $`1` (or $`-1`) through the multiples
of $`k`: the points move around $`\mathbb{R}/\mathbb{Z}` in steps shorter than the complementary arc,
which has length $`1 - 2\eta,` so one of a bounded number of them lands in it. The bound depends on
$`\eta` and $`s` only, not on $`Z`.
:::

:::lemma_ "lemma:active-step" (parent := "lower-bound") (lean := "CriticalRadiusFive.level_mem_band, CriticalRadiusFive.level_ne_of_isCutLevel")
*No step of the walk crosses a cut level.* Let $`r^2 < 3 + \varphi`, and let $`q_+` and $`q_-` be
cut levels in the sense of {uses "lemma:cut-levels"}[] for the centre $`Z_p` of
{uses "lemma:window"}[], with $`\delta = 3 - \varphi`, $`s = -\alpha` and $`L = L(r)`. Let
$`v, v' \in W_p(r)` be joined by a typed step: $`v' = v + e` with $`\operatorname{cl}(v) = 0`, or
$`v' = v - e` with $`\operatorname{cl}(v) = 1`, for some $`e \in \mu_5`. If
$`5q_- < \ell(v) \le 5q_+`, then $`5q_- < \ell(v') \le 5q_+`. The same holds for $`\ell_2`, with the
centre $`Z'_p`.
:::

:::proof "lemma:active-step"
Use the step table {uses "lemma:step-table"}[]. A step out of class $`0` adds $`e` and changes the
level by $`\ell(e) \in \{3, -2\}`; since $`\ell(v) \equiv 0 \pmod 5`, the bound $`\ell(v) \le 5q_+`
survives unless $`\ell(e) = 3` and $`\ell(v) = 5q_+`, while $`\ell(v) > 5q_-` forces
$`\ell(v) \ge 5q_- + 5` and survives. A step out of class $`1` subtracts $`e`; since
$`\ell(v) \equiv 3 \pmod 5`, the bound $`\ell(v) \le 5q_+` forces $`\ell(v) \le 5q_+ - 2` and
survives, while $`\ell(v) > 5q_-` forces $`\ell(v) \ge 5q_- + 3` and survives unless
$`\ell(e) = 3` and $`\ell(v) = 5q_- + 3`, in which case the step arrives at the class-$`0` point
$`v - e` at level exactly $`5q_-`. So in both exceptional cases an active step $`e` joins a point
$`w` at level $`5q`, with $`q = q_+` or $`q = q_-`, to the point $`w + e`. The statement concerns
only steps between two points of the window, so both $`w` and $`w + e` lie in $`W_p(r)`, and by
{uses "lemma:window"}[] the value $`\psi_u(w) = \delta P - \delta\alpha q` lies within $`L(r)` of
$`Z_p`: then $`q` is not a cut level, a contradiction. The same argument, with $`\psi_{\zeta u}` and
$`Z'_p`, applies to $`\ell_2`.
:::

:::theorem "thm:confinement" (parent := "lower-bound") (lean := "CriticalRadiusFive.IsCutLevel, CriticalRadiusFive.exists_isCutLevel, CriticalRadiusFive.edgeClosed_cutSet, CriticalRadiusFive.good_cutSet, CriticalRadiusFive.mem_box_of_mem_cutSet")
*Confinement.* Let $`0 \le r < \sqrt{3+\varphi}`, and write $`u_1 := u`, $`u_2 := \zeta u` for the two
functionals $`\psi_{u_1}, \psi_{u_2}` and $`\ell_1 := \ell`, $`\ell_2` for their levels
({bpref "def:level"}[]). There is $`N`, depending only on $`r`, such that for every $`p` the pivots
and tips of the walk of $`p` that lie in the window stay in two bands,
$`5q_-^{(i)} < \ell_i \le 5q_+^{(i)}` for $`i = 1, 2`, between cut levels $`q_\pm^{(i)}` of
$`\psi_{u_i}` with $`1 \le |q_\pm^{(i)}| \le N`. Hence every orbit of $`\mathrm{GG}_5(r)` lies in a
finite set of at most $`M(r)` points, with $`M(r)` independent of $`p`. (The formal proof assembles
this uniform bound inside the proof of `finite_GG_five_of_lt`, {bpref "thm:lower"}[]; the
declarations linked here are its ingredients.)
:::

:::proof "thm:confinement"
If $`p` lies outside both disks, its orbit is $`\{p\}`; otherwise $`|p| \le 1 + r`. Let
$`Z_p^{(1)} := Z_p` and $`Z_p^{(2)} := Z'_p` be the centres of {uses "lemma:window"}[] for the two
functionals. By {uses "lemma:window-lt-period"}[], $`2L(r) < \delta`, so {uses "lemma:cut-levels"}[]
(with $`s = -\alpha` and $`L = L(r)`) gives $`N`, depending only on $`r`, and cut levels
$`q_+^{(i)} \in [1, N]` and $`q_-^{(i)} \in [-N, -1]` for $`Z_p^{(1)}` and $`Z_p^{(2)}`.

Let $`V` consist of the lattice points $`v` of the window, of class $`0` or $`1`, with
$`5q_-^{(i)} < \ell_i(v) \le 5q_+^{(i)}` for $`i = 1, 2`. Since $`p` lies in one of the disks, the
starting pivot $`0` (if $`p \in D_-`) or the starting tip $`1` (if $`p \in D_+`) lies in the window,
and their levels ($`0` and $`3` for $`\ell_1`, $`0` and $`-2` for $`\ell_2`) lie in the bands. A
typed step from a point of $`V` to a point of the window lands in class $`0` or $`1`, and by
{uses "lemma:active-step"}[], applied to $`\ell_1` and to $`\ell_2`, it stays in both bands. So $`V`
is closed in the sense of {uses "lemma:typed-walk"}[], and every point of the orbit of $`p` is
$`m(p + 1 - 2\nu) - 1` with $`m \in \mu_5` and $`\nu \in V` or $`\nu + \overline{m} \in V`.

Discreteness. Every $`v \in V` has $`|v| \le 1 + r`, hence $`|\psi_{u_i}(v)| \le 2 + 2r`, and
$`|\ell_i(v)| \le 5N`. Write $`\psi_{u_i}(v) = A_i + B_i\varphi`. Then
$`\psi_{u_i}(v) + \ell_i(v) = -\delta B_i` bounds the integers $`B_1, \ell_1(v), B_2, \ell_2(v)`,
which determine $`v` through an integer matrix of determinant $`-5`; so $`V` lies in a box of
lattice points whose size depends only on $`r`. The points $`m(p + 1 - 2\nu) - 1` with
$`m \in \mu_5` and $`\nu` or $`\nu + \overline{m}` in $`V` are therefore at most $`M(r)` in number,
independently of $`p`.

Conceptually, this is the discreteness of $`\mathbb{Z}[\zeta]` in $`\mathbb{C} \times \mathbb{C}`
under $`v \mapsto (v, \sigma(v))`, where $`\sigma` is the Galois automorphism $`\zeta \mapsto \zeta^2`:
the Galois conjugate $`A_i + B_i(1 - \varphi) = \varphi^2\psi_{u_i}(v) + \varphi\ell_i(v)` is bounded
as well; it is the value at $`\sigma(v)` of a functional, and the two functionals have independent
directions, so $`\sigma(v)` is bounded too.
:::

:::theorem "thm:lower" (parent := "lower-bound") (lean := "CriticalRadiusFive.finite_GG_five_of_lt") (uses := "def:group")
*The lower bound.* For every $`r < \sqrt{3+\varphi}`, $`\mathrm{GG}_5(r)` is finite.
:::

:::proof "thm:lower"
For $`r < 0` both turns are the identity. For $`0 \le r < \sqrt{3+\varphi}`,
{uses "thm:confinement"}[] bounds every orbit by $`M(r)`, and $`\mathrm{GG}_5(r)` is generated by the
two turns, so {uses "thm:bounded-orbits"}[] shows that it is finite.
:::
