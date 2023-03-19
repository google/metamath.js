include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "cardid2.mm"
include "ensymd.mm"
include "entr.mm"
include "expcom.mm"
include "syl.mm"
include "impbid.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "cardval3.mm"
include "cardon.mm"
include "oncardval.mm"
include "mp1i.mm"
include "3eqtr4rd.mm"
include "wn.mm"
include "c0.mm"
include "card0.mm"
include "ndmfv.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem cardidm
  let cA: class A
  let vy: setvar y


  assert |- ( card ` ( card ` A ) ) = ( card ` A )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    cA
    ccrd
    cfv
    #
    ccrd
    cfv
    #
    @1
    wceq
    @0
    vy
    cv
    #
    cA
    cen
    wbr
    #
    vy
    con0
    crab
    #
    cint
    @3
    @1
    cen
    wbr
    #
    vy
    con0
    crab
    #
    cint
    #
    @1
    @2
    @0
    @5
    @7
    @0
    @4
    @6
    vy
    con0
    @0
    @4
    @6
    @0
    cA
    @1
    cen
    wbr
    #
    @4
    @6
    wi
    @0
    @1
    cA
    cA
    cardid2
    #
    ensymd
    @4
    @9
    @6
    @3
    cA
    @1
    entr
    expcom
    syl
    @0
    @1
    cA
    cen
    wbr
    #
    @6
    @4
    wi
    @10
    @6
    @11
    @4
    @3
    @1
    cA
    entr
    expcom
    syl
    impbid
    rabbidv
    inteqd
    vy
    cA
    cardval3
    @1
    con0
    wcel
    @2
    @8
    wceq
    @0
    cA
    cardon
    vy
    @1
    oncardval
    mp1i
    3eqtr4rd
    @0
    wn
    #
    c0
    ccrd
    cfv
    c0
    @2
    @1
    card0
    @12
    @1
    c0
    ccrd
    cA
    ccrd
    ndmfv
    #
    fveq2d
    @13
    3eqtr4a
    pm2.61i
end
