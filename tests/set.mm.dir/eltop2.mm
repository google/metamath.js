include "ctop.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "tgtop.mm"
include "eleq2d.mm"
include "eltg2b.mm"
include "bitr3d.mm"

theorem eltop2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cJ: class J
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let cV: class V
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint J y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint J w
  disjoint J z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint C y
  assert |- ( J e. Top -> ( A e. J <-> A. x e. A E. y e. J ( x e. y /\ y C_ A ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    ctg
    cfv
    #
    wcel
    cA
    cJ
    wcel
    vx
    cv
    vy
    cv
    #
    wcel
    @2
    cA
    wss
    wa
    vy
    cJ
    wrex
    vx
    cA
    wral
    @0
    @1
    cJ
    cA
    cJ
    tgtop
    eleq2d
    vx
    vy
    cA
    cJ
    ctop
    eltg2b
    bitr3d
end
