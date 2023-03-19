include "ctsk.mm"
include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "ccrd.mm"
include "cdm.mm"
include "wi.mm"
include "wral.mm"
include "elpwi.mm"
include "tskssel.mm"
include "3exp.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "rabss.mm"
include "sylibr.mm"
include "tskwe.mm"
include "mpdan.mm"

theorem tskwe2
  let cT: class T
  let vy: setvar y


  assert |- ( T e. Tarski -> T e. dom card )

  proof
    cT
    ctsk
    wcel
    #
    vy
    cv
    #
    cT
    csdm
    wbr
    #
    vy
    cT
    cpw
    #
    crab
    cT
    wss
    #
    cT
    ccrd
    cdm
    wcel
    @0
    @2
    @1
    cT
    wcel
    #
    wi
    #
    vy
    @3
    wral
    @4
    @0
    @6
    vy
    @3
    @1
    @3
    wcel
    @1
    cT
    wss
    #
    @0
    @6
    @1
    cT
    elpwi
    @0
    @7
    @2
    @5
    @1
    cT
    tskssel
    3exp
    syl5
    ralrimiv
    @2
    vy
    @3
    cT
    rabss
    sylibr
    vy
    cT
    ctsk
    tskwe
    mpdan
end
