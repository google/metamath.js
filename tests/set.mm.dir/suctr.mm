include "wtr.mm"
include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wo.mm"
include "elsuci.mm"
include "trel.mm"
include "expdimp.mm"
include "eleq2.mm"
include "biimpcd.mm"
include "adantl.mm"
include "jaod.mm"
include "syl5.mm"
include "expimpd.mm"
include "elelsuc.mm"
include "syl6.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "sylibr.mm"

theorem suctr
  let cA: class A
  let vy: setvar y
  let vz: setvar z


  assert |- ( Tr A -> Tr suc A )

  proof
    cA
    wtr
    #
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @2
    cA
    csuc
    #
    wcel
    #
    wa
    #
    @1
    @4
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    @4
    wtr
    @0
    @8
    vz
    vy
    @0
    @6
    @1
    cA
    wcel
    #
    @7
    @0
    @3
    @5
    @9
    @5
    @2
    cA
    wcel
    #
    @2
    cA
    wceq
    #
    wo
    @0
    @3
    wa
    #
    @9
    @2
    cA
    elsuci
    @12
    @10
    @9
    @11
    @0
    @3
    @10
    @9
    cA
    @1
    @2
    trel
    expdimp
    @3
    @11
    @9
    wi
    @0
    @11
    @3
    @9
    @2
    cA
    @1
    eleq2
    biimpcd
    adantl
    jaod
    syl5
    expimpd
    @1
    cA
    elelsuc
    syl6
    alrimivv
    vz
    vy
    @4
    dftr2
    sylibr
end
