include "cv.mm"
include "crpss.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wpo.mm"
include "wa.mm"
include "wss.mm"
include "wo.mm"
include "wor.mm"
include "porpss.mm"
include "biantrur.mm"
include "wpss.mm"
include "sspsstri.mm"
include "vex.mm"
include "brrpss.mm"
include "biid.mm"
include "3orbi123i.mm"
include "bitr4i.mm"
include "2ralbii.mm"
include "df-so.mm"
include "3bitr4ri.mm"

theorem sorpss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( [C.] Or A <-> A. x e. A A. y e. A ( x C_ y \/ y C_ x ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    crpss
    wbr
    #
    vx
    vy
    weq
    #
    @1
    @0
    crpss
    wbr
    #
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    cA
    crpss
    wpo
    #
    @6
    wa
    @0
    @1
    wss
    @1
    @0
    wss
    wo
    #
    vy
    cA
    wral
    vx
    cA
    wral
    cA
    crpss
    wor
    @7
    @6
    cA
    porpss
    biantrur
    @8
    @5
    vx
    vy
    cA
    cA
    @8
    @0
    @1
    wpss
    #
    @3
    @1
    @0
    wpss
    #
    w3o
    @5
    @0
    @1
    sspsstri
    @2
    @9
    @3
    @3
    @4
    @10
    @0
    @1
    vy
    vex
    brrpss
    @3
    biid
    @1
    @0
    vx
    vex
    brrpss
    3orbi123i
    bitr4i
    2ralbii
    vx
    vy
    cA
    crpss
    df-so
    3bitr4ri
end
