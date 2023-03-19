include "wtr.mm"
include "wel.mm"
include "cv.mm"
include "csuc.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "sssucid.mm"
include "trel.mm"
include "expd.mm"
include "adantrd.mm"
include "ssel.mm"
include "ee03.mm"
include "simpl.mm"
include "a1i.mm"
include "eleq2.mm"
include "biimpcd.mm"
include "syl6.mm"
include "simpr.mm"
include "elsuci.mm"
include "jao.mm"
include "ee222.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "sylibr.mm"

theorem suctrALT2
  let cA: class A
  let vz: setvar z
  let vy: setvar y


  assert |- ( Tr A -> Tr suc A )

  proof
    cA
    wtr
    #
    vz
    vy
    wel
    #
    vy
    cv
    #
    cA
    csuc
    #
    wcel
    #
    wa
    #
    vz
    cv
    #
    @3
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    @3
    wtr
    @0
    @8
    vz
    vy
    @0
    @5
    @2
    cA
    wcel
    #
    @7
    wi
    @2
    cA
    wceq
    #
    @7
    wi
    @9
    @10
    wo
    #
    @7
    cA
    @3
    wss
    #
    @0
    @5
    @9
    @6
    cA
    wcel
    #
    @7
    cA
    sssucid
    #
    @0
    @1
    @9
    @13
    wi
    @4
    @0
    @1
    @9
    @13
    cA
    @6
    @2
    trel
    expd
    adantrd
    cA
    @3
    @6
    ssel
    #
    ee03
    @12
    @0
    @5
    @10
    @13
    @7
    @14
    @0
    @5
    @1
    @10
    @13
    wi
    @5
    @1
    wi
    @0
    @1
    @4
    simpl
    a1i
    @10
    @1
    @13
    @2
    cA
    @6
    eleq2
    biimpcd
    syl6
    @15
    ee03
    @0
    @5
    @4
    @11
    @5
    @4
    wi
    @0
    @1
    @4
    simpr
    a1i
    @2
    cA
    elsuci
    syl6
    @9
    @7
    @10
    jao
    ee222
    alrimivv
    vz
    vy
    @3
    dftr2
    sylibr
end
