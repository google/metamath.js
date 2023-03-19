include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "wbr.mm"
include "wi.mm"
include "fvex.mm"
include "cv.mm"
include "neeq1.mm"
include "weu.mm"
include "wb.mm"
include "tz6.12-2.mm"
include "necon1ai.mm"
include "tz6.12c.mm"
include "syl.mm"
include "biimpcd.mm"
include "sylbird.mm"
include "eqcoms.mm"
include "breq2.mm"
include "3imtr3d.mm"
include "vtocle.mm"
include "a1i.mm"
include "com12.mm"

theorem tz6.12i
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y


  assert |- ( B =/= (/) -> ( ( F ` A ) = B -> A F B ) )

  proof
    cA
    cF
    cfv
    #
    cB
    wceq
    #
    cB
    c0
    wne
    #
    cA
    cB
    cF
    wbr
    #
    @1
    @0
    c0
    wne
    #
    cA
    @0
    cF
    wbr
    #
    @2
    @3
    @4
    @5
    wi
    #
    @1
    @6
    vy
    @0
    cA
    cF
    fvex
    vy
    cv
    #
    @0
    wceq
    @7
    c0
    wne
    #
    cA
    @7
    cF
    wbr
    #
    @4
    @5
    @8
    @9
    wi
    @0
    @7
    @0
    @7
    wceq
    #
    @8
    @4
    @9
    @0
    @7
    c0
    neeq1
    @4
    @10
    @9
    @4
    @9
    vy
    weu
    #
    @10
    @9
    wb
    @11
    @0
    c0
    vy
    cA
    cF
    tz6.12-2
    necon1ai
    vy
    cA
    cF
    tz6.12c
    syl
    biimpcd
    sylbird
    eqcoms
    @7
    @0
    c0
    neeq1
    @7
    @0
    cA
    cF
    breq2
    3imtr3d
    vtocle
    a1i
    @0
    cB
    c0
    neeq1
    @0
    cB
    cA
    cF
    breq2
    3imtr3d
    com12
end
