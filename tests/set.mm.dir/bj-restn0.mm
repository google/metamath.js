include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "wex.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "n0.mm"
include "wi.mm"
include "vex.mm"
include "inex1.mm"
include "isseti.mm"
include "jctr.mm"
include "eximi.mm"
include "df-rex.mm"
include "sylibr.mm"
include "rexcom4.mm"
include "sylib.mm"
include "a1i.mm"
include "syl5bi.mm"
include "elrest.mm"
include "biimprd.mm"
include "eximdv.mm"
include "syld.mm"
include "syl6ibr.mm"

theorem bj-restn0
  let cA: class A
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( X e. V /\ A e. W ) -> ( X =/= (/) -> ( X |`t A ) =/= (/) ) )

  proof
    cX
    cV
    wcel
    cA
    cW
    wcel
    wa
    #
    cX
    c0
    wne
    #
    vx
    cv
    #
    cX
    cA
    crest
    co
    #
    wcel
    #
    vx
    wex
    #
    @3
    c0
    wne
    @0
    @1
    @2
    vy
    cv
    #
    cA
    cin
    #
    wceq
    #
    vy
    cX
    wrex
    #
    vx
    wex
    #
    @5
    @1
    @6
    cX
    wcel
    #
    vy
    wex
    #
    @0
    @10
    vy
    cX
    n0
    @12
    @10
    wi
    @0
    @12
    @8
    vx
    wex
    #
    vy
    cX
    wrex
    #
    @10
    @12
    @11
    @13
    wa
    #
    vy
    wex
    @14
    @11
    @15
    vy
    @11
    @13
    vx
    @7
    @6
    cA
    vy
    vex
    inex1
    isseti
    jctr
    eximi
    @13
    vy
    cX
    df-rex
    sylibr
    @8
    vy
    vx
    cX
    rexcom4
    sylib
    a1i
    syl5bi
    @0
    @9
    @4
    vx
    @0
    @4
    @9
    vy
    @2
    cA
    cX
    cV
    cW
    elrest
    biimprd
    eximdv
    syld
    vx
    @3
    n0
    syl6ibr
end
