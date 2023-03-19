include "ctop.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "tgtop.mm"
include "eleq2d.mm"
include "eltg3.mm"
include "bitr3d.mm"

theorem eltop3
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let cV: class V
  let cC: class C

  disjoint A x
  disjoint J x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
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
  disjoint J y
  disjoint J z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint C y
  assert |- ( J e. Top -> ( A e. J <-> E. x ( x C_ J /\ A = U. x ) ) )

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
    #
    cJ
    wss
    cA
    @2
    cuni
    wceq
    wa
    vx
    wex
    @0
    @1
    cJ
    cA
    cJ
    tgtop
    eleq2d
    vx
    cA
    cJ
    ctop
    eltg3
    bitr3d
end
