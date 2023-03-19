include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "ctg.mm"
include "cfv.mm"
include "eltg3.mm"
include "abbi2dv.mm"

theorem tgval3
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint V x
  disjoint V y
  disjoint x z
  disjoint A x
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
  disjoint B z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V z
  disjoint C x
  disjoint C y
  assert |- ( B e. V -> ( topGen ` B ) = { x | E. y ( y C_ B /\ x = U. y ) } )

  proof
    cB
    cV
    wcel
    vy
    cv
    #
    cB
    wss
    vx
    cv
    #
    @0
    cuni
    wceq
    wa
    vy
    wex
    vx
    cB
    ctg
    cfv
    vy
    @1
    cB
    cV
    eltg3
    abbi2dv
end
