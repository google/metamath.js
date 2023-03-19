include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "supval2.mm"
include "wreu.mm"
include "wcel.mm"
include "supeu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem supcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let vw: setvar w
  let cC: class C
  assume supmo.1: |- ( ph -> R Or A )
  assume supcl.2: |- ( ph -> E. x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint B w
  disjoint C w
  disjoint ph w
  assert |- ( ph -> sup ( B , A , R ) e. A )

  proof
    wph
    cB
    cA
    cR
    csup
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    @1
    @0
    cR
    wbr
    @1
    vz
    cv
    cR
    wbr
    vz
    cB
    wrex
    wi
    vy
    cA
    wral
    wa
    #
    vx
    cA
    crio
    #
    cA
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    supmo.1
    supval2
    wph
    @2
    vx
    cA
    wreu
    @3
    cA
    wcel
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    supmo.1
    supcl.2
    supeu
    @2
    vx
    cA
    riotacl
    syl
    eqeltrd
end
