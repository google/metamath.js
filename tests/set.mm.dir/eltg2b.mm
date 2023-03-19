include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "eltg2.mm"
include "simpl.mm"
include "reximi.mm"
include "eluni2.mm"
include "sylibr.mm"
include "ralimi.mm"
include "dfss3.mm"
include "pm4.71ri.mm"
include "syl6bbr.mm"

theorem eltg2b
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint V x
  disjoint V y
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
  disjoint B z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V z
  disjoint C x
  disjoint C y
  assert |- ( B e. V -> ( A e. ( topGen ` B ) <-> A. x e. A E. y e. B ( x e. y /\ y C_ A ) ) )

  proof
    cB
    cV
    wcel
    cA
    cB
    ctg
    cfv
    wcel
    cA
    cB
    cuni
    #
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @3
    cA
    wss
    #
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    wa
    @8
    vx
    vy
    cA
    cB
    cV
    eltg2
    @8
    @1
    @8
    @2
    @0
    wcel
    #
    vx
    cA
    wral
    @1
    @7
    @9
    vx
    cA
    @7
    @4
    vy
    cB
    wrex
    @9
    @6
    @4
    vy
    cB
    @4
    @5
    simpl
    reximi
    vy
    @2
    cB
    eluni2
    sylibr
    ralimi
    vx
    cA
    @0
    dfss3
    sylibr
    pm4.71ri
    syl6bbr
end
