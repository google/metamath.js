include "cep.mm"
include "wwe.mm"
include "wor.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "w3o.mm"
include "weso.mm"
include "wbr.mm"
include "solin.mm"
include "epel.mm"
include "biid.mm"
include "3orbi123i.mm"
include "sylib.mm"
include "sylan.mm"

theorem wecmpep
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( ( _E We A /\ ( x e. A /\ y e. A ) ) -> ( x e. y \/ x = y \/ y e. x ) )

  proof
    cA
    cep
    wwe
    cA
    cep
    wor
    #
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cA
    wcel
    wa
    #
    @1
    @2
    wcel
    #
    vx
    vy
    weq
    #
    @2
    @1
    wcel
    #
    w3o
    #
    cA
    cep
    weso
    @0
    @3
    wa
    @1
    @2
    cep
    wbr
    #
    @5
    @2
    @1
    cep
    wbr
    #
    w3o
    @7
    cA
    @1
    @2
    cep
    solin
    @8
    @4
    @5
    @5
    @9
    @6
    vx
    vy
    epel
    @5
    biid
    vy
    vx
    epel
    3orbi123i
    sylib
    sylan
end
