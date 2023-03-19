include "wtr.mm"
include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wo.mm"
include "simpr.mm"
include "vex.mm"
include "elsuc.mm"
include "sylib.mm"
include "simpl.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "elelsuc.mm"
include "syl6.mm"
include "trel.mm"
include "expd.mm"
include "adantrd.mm"
include "syl8.mm"
include "jao.mm"
include "mpdi.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "sylibr.mm"

theorem suctrOLD
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
    @2
    cA
    wcel
    #
    @2
    cA
    wceq
    #
    wo
    #
    @7
    @6
    @5
    @11
    @3
    @5
    simpr
    @2
    cA
    vy
    vex
    elsuc
    sylib
    @0
    @6
    @10
    @7
    wi
    #
    @11
    @7
    wi
    #
    @6
    @10
    @1
    cA
    wcel
    #
    @7
    @6
    @3
    @10
    @14
    @3
    @5
    simpl
    @2
    cA
    @1
    eleq2
    syl5ibcom
    @1
    cA
    elelsuc
    #
    syl6
    @0
    @6
    @9
    @7
    wi
    @12
    @13
    wi
    @0
    @6
    @9
    @14
    @7
    @0
    @3
    @9
    @14
    wi
    @5
    @0
    @3
    @9
    @14
    cA
    @1
    @2
    trel
    expd
    adantrd
    @15
    syl8
    @9
    @7
    @10
    jao
    syl6
    mpdi
    mpdi
    alrimivv
    vz
    vy
    @4
    dftr2
    sylibr
end
