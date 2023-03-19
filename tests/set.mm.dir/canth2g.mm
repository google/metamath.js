include "cv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "pweq.mm"
include "breq12.mm"
include "mpdan.mm"
include "vex.mm"
include "canth2.mm"
include "vtoclg.mm"

theorem canth2g
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> A ~< ~P A )

  proof
    vx
    cv
    #
    @0
    cpw
    #
    csdm
    wbr
    #
    cA
    cA
    cpw
    #
    csdm
    wbr
    #
    vx
    cA
    cV
    @0
    cA
    wceq
    @1
    @3
    wceq
    @2
    @4
    wb
    @0
    cA
    pweq
    @0
    cA
    @1
    @3
    csdm
    breq12
    mpdan
    @0
    vx
    vex
    canth2
    vtoclg
end
