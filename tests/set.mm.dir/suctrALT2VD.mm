include "wtr.mm"
include "csuc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "dftr2.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "sssucid.mm"
include "idn1.mm"
include "idn2.mm"
include "simpl.mm"
include "e2.mm"
include "idn3.mm"
include "trel.mm"
include "expd.mm"
include "e123.mm"
include "ssel.mm"
include "e03.mm"
include "in3.mm"
include "eleq2.mm"
include "biimpcd.mm"
include "e23.mm"
include "simpr.mm"
include "elsuci.mm"
include "jao.mm"
include "e222.mm"
include "in2.mm"
include "gen12.mm"
include "biimpr.mm"
include "e01.mm"
include "in1.mm"

theorem suctrALT2VD
  let cA: class A
  let vz: setvar z
  let vy: setvar y


  assert |- ( Tr A -> Tr suc A )

  proof
    cA
    wtr
    #
    cA
    csuc
    #
    wtr
    #
    @2
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    @3
    @1
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    #
    wb
    @0
    @10
    @2
    vz
    vy
    @1
    dftr2
    @0
    @9
    vz
    vy
    @0
    @7
    @8
    @0
    @7
    @4
    cA
    wcel
    #
    @8
    wi
    @4
    cA
    wceq
    #
    @8
    wi
    @11
    @12
    wo
    #
    @8
    @0
    @7
    @11
    @8
    cA
    @1
    wss
    #
    @0
    @7
    @11
    @3
    cA
    wcel
    #
    @8
    cA
    sssucid
    #
    @0
    @0
    @7
    @5
    @11
    @11
    @15
    @0
    idn1
    @0
    @7
    @7
    @5
    @0
    @7
    idn2
    #
    @5
    @6
    simpl
    e2
    #
    @0
    @7
    @11
    idn3
    @0
    @5
    @11
    @15
    cA
    @3
    @4
    trel
    expd
    e123
    cA
    @1
    @3
    ssel
    #
    e03
    in3
    @0
    @7
    @12
    @8
    @14
    @0
    @7
    @12
    @15
    @8
    @16
    @0
    @7
    @5
    @12
    @12
    @15
    @18
    @0
    @7
    @12
    idn3
    @12
    @5
    @15
    @4
    cA
    @3
    eleq2
    biimpcd
    e23
    @19
    e03
    in3
    @0
    @7
    @6
    @13
    @0
    @7
    @7
    @6
    @17
    @5
    @6
    simpr
    e2
    @4
    cA
    elsuci
    e2
    @11
    @8
    @12
    jao
    e222
    in2
    gen12
    @2
    @10
    biimpr
    e01
    in1
end
