include "ccllaw.mm"
include "wbr.mm"
include "wcel.mm"
include "co.mm"
include "cvv.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "df-cllaw.mm"
include "bropaex12.mm"
include "iscllaw.mm"
include "ovrspc2v.mm"
include "expcom.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "3impib.mm"

theorem clcllaw
  let cM: class M
  let cX: class X
  let cY: class Y
  let c.op: class .o.
  let vm: setvar m
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( ( .o. clLaw M /\ X e. M /\ Y e. M ) -> ( X .o. Y ) e. M )

  proof
    c.op
    cM
    ccllaw
    wbr
    #
    cX
    cM
    wcel
    #
    cY
    cM
    wcel
    #
    cX
    cY
    c.op
    co
    cM
    wcel
    #
    c.op
    cvv
    wcel
    cM
    cvv
    wcel
    wa
    #
    @0
    @1
    @2
    wa
    #
    @3
    wi
    #
    vx
    cv
    #
    vy
    cv
    #
    vo
    cv
    co
    vm
    cv
    #
    wcel
    vy
    @9
    wral
    vx
    @9
    wral
    vo
    vm
    c.op
    cM
    ccllaw
    vx
    vy
    vm
    vo
    df-cllaw
    bropaex12
    @4
    @0
    @7
    @8
    c.op
    co
    cM
    wcel
    vy
    cM
    wral
    vx
    cM
    wral
    #
    @6
    vx
    vy
    cM
    cvv
    cvv
    c.op
    iscllaw
    @5
    @10
    @3
    vx
    vy
    cM
    cM
    cM
    c.op
    cX
    cY
    ovrspc2v
    expcom
    syl6bi
    mpcom
    3impib
end
