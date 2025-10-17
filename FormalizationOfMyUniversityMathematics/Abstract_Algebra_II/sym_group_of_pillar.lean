import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.OrderOfElement

#check List.formPerm
#eval [1,2,3,4].map [1,2,4,3].formPerm
-- #eval orderOf [1,2,4,3].formPerm


/-
let E ⊆ ℝ³ = vertice of hexagonal pillar
let x ∈ E be vertix 1
let σ be rotate along vertical axis 60°
let h be reflect along horizantal plane
let r = d(x, σx)
let R = d(x, hx)

let S₁₂ be permution group of E.
let G ⊆ S₁₂ be a subgroup satisfy the following properties
1. ∀ y,z ∈ E, d(y,z) = d(gy, gz)
2. ∀ y ∈ E, {z | d(y,z) = r} = {σy, σ⁻¹y}
3. ∀ y ∈ E, {z | d(y,z) = R} = {hy}

indeed, σ, h ∈ G, σh = hσ and E = {hᵐσⁿx | m=0,1, n=1~6}

Claim1:
let g ∈ G, if g(x) = x, g(σ(x)) = σ(x) then g = e

Proof:

Consider
r
= d(σx, x)
= d(σ²x, σx)
= d(gσ²x, gσx)
= d(gσ²x, σx)
→ gσ²x = σ²x, x
→ gσ²x = σ²x

r
= d(σx, x)
= d(σ³x, σ²x)
= d(gσ³x, gσ²x)
= d(gσ³x, σ²x)
→ gσ³x = σ³x, σ²x
→ gσ³x = σ³x

repeat this process, we can get
→ gσⁿx = σⁿx for all n = 0~5

For top face vertice
let n = 0~5
R
= d(hx, x)
= d(σⁿhx, σⁿx)
= d(hσⁿx, σⁿx)
= d(ghσⁿx, gσⁿx)
= d(ghσⁿx, σⁿx)
→ ghσⁿx = hσⁿx

→ g fix all hᵐσⁿx, m = 0,1, n = 0~5
and E = {hᵐσⁿx | m=0,1, n=1~6}
→ g fix E
→ g = e



Claim2
|Stab_G(x)| ≤ 2

let g₁, g₂ ∈ Stab_G(x) with g₁ ≠ g₂
→ r
= d(σx, x)
= d(gᵢσx, gᵢx)
= d(gᵢσx, x)
→ gᵢσx = σ⁻¹x, σx for i = 1,2
wlog, let g₁σx = σx, g₂σx = σ⁻¹x

given g ∈ Stab_G(x)
we want to show g = g₁ or g₂

r
= d(σx, x)
= d(gσx, gx)
= d(gσx, x)
→ gσx = σ⁻¹x, σx
→ gσx = gᵢσx for some i = 1,2

now, we have
gᵢ⁻¹gσx = σx
gᵢ⁻¹gx = x
by claim, gᵢ⁻¹g = e → g = gᵢ

this show |Stab_G(x)| ≤ 2


-/

/-

(a)
by direct calculation, we have
Stab_G(x) ⊇ {e, (26)(35)(8 12)(9 11)}
(just write e for indentity is enough,
do not have to write (1)(2)(3)...(11)(12) or () )

by why Stab_G(x) ⊆ {e, (26)(35)(8 12)(9 11)}
notice if g ∈ Stab_G(x)
g will fix distance between vertex 1,2 and vertex 1
thus g(2) = 2 or 6
exactly correspons to e, (26)(35)(8 12)(9 11)
denote g₁ = e, g₂ = (26)(35)(8 12)(9 11)
if there exist other g' ∈ Stab_G(x)
then g'2 = gᵢ2 for some i = 1,2
now we have g₀ := gᵢ⁻¹g' will fix vertix 1,2 and preserve distance
compare distance between all vertix to vertix1,2
we can see g₀ must fix all vertix
and so gᵢ⁻¹g' = g₀ = e →  g' = gᵢ
thus show we exactly have Stab_G(x) = {e, (26)(35)(8 12)(9 11)}


(b)
in the proof of Orbit-Stabilizer Theorem
we see if g₀ ∈ G saticfy g₀1 = 2 then {g ∈ G| g1 = 2} = g₀Stab_G(1)
we can take g₀ = (123456)(7 8 9 10 11 12),indeed g₀1 = 2
and so
{g ∈ G| g1 = 2}
= g₀Stab_G(1)
= {(123456)(7 8 9 10 11 12), (12)(36)(45)(78)(9 12)(10 11)}

(c)
Indeed, use
σ = (123456)(7 8 9 10 11 12) be rotate along vertical axis 60°
h = (17)(28)(39)(4 10)(5 11)(6 12) be reflect along horizantal plane )
one can send vertex 1 to all vertices
thus |Gx| = 12
by Orbit-Stabilizer Theorem
|G| = |Gx||Stab_G(x)| = 12*2 = 24

(d)
if G ≅ Dₙ for some n ∈ ℕ → 24 = |G| = |Dₙ| = 2n → n = 12
consider the structural property
"a group contain a element of order 12 or not"
D₁₂ have a element of order 12, namely, σ ∈ D₁₂
but Do G not contain a element of order 12?
the insteresting fact is, G do not only contain rotation and reflection
G also contain a symmetry so call "[Improper rotation](https://en.wikipedia.org/wiki/Improper_rotation)"
they are rotation compose with a reflection
for rotation, if it order = 12, the hexagonal pillar
need to contain a place where there are 12 vertice on it,
it is impossple
for refaltion, all reflection ar order 2
for improper rotation, by direct calculation
we have four improper rotation
(let σ = (123456)(7 8 9 10 11 12) be rotate along vertical axis 60°
let h = (17)(28)(39)(4 10)(5 11)(6 12) be reflect along horizantal plane )
1. σh = (1 8 3 10 5 12)(7 2 9 4 11 6)
2. σ⁻¹h = (12 5 10 3 8 1)(6 11 4 9 2 7)
3. σ²h = (1 9 5 7 3 11)(2 10 6 8 4 12)
4. σ⁻²h = (11 3 7 5 9 1)(12 4 8 6 10 2)
(notice σ³h are point reflection the center of hexagonal pillar, also call inversion)
lucky they are all order 6
thus we conclude G do not contain a element of order 12
and so G do not isomphic to Dₙ for any n ∈ ℕ.
-/
