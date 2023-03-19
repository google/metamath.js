include "cxr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "csn.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc1.mm"
include "anidms.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "clt.mm"
include "wn.mm"
include "xrlenlt.mm"
include "ancoms.mm"
include "xrlttri3.mm"
include "biimprd.mm"
include "expcomd.mm"
include "sylbid.mm"
include "com23.mm"
include "ex.mm"
include "3impd.mm"
include "eleq1a.mm"
include "xrleid.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "breq1.mm"
include "3jcad.mm"
include "impbid.mm"
include "velsn.mm"
include "syl6bbr.mm"
include "bitrd.mm"
include "eqrdv.mm"

theorem iccid
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A e. RR* -> ( A [,] A ) = { A } )

  proof
    cA
    cxr
    wcel
    #
    vx
    cA
    cA
    cicc
    co
    #
    cA
    csn
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @3
    cxr
    wcel
    #
    cA
    @3
    cle
    wbr
    #
    @3
    cA
    cle
    wbr
    #
    w3a
    #
    @3
    @2
    wcel
    #
    @0
    @4
    @8
    wb
    cA
    cA
    @3
    elicc1
    anidms
    @0
    @8
    @3
    cA
    wceq
    #
    @9
    @0
    @8
    @10
    @0
    @5
    @6
    @7
    @10
    @0
    @5
    @6
    @7
    @10
    wi
    #
    wi
    @0
    @5
    wa
    #
    @6
    @3
    cA
    clt
    wbr
    wn
    #
    @11
    cA
    @3
    xrlenlt
    @12
    @7
    @13
    @10
    @12
    @7
    cA
    @3
    clt
    wbr
    wn
    #
    @13
    @10
    wi
    @5
    @0
    @7
    @14
    wb
    @3
    cA
    xrlenlt
    ancoms
    @12
    @13
    @14
    @10
    @5
    @0
    @13
    @14
    wa
    #
    @10
    wi
    @5
    @0
    wa
    @10
    @15
    @3
    cA
    xrlttri3
    biimprd
    ancoms
    expcomd
    sylbid
    com23
    sylbid
    ex
    3impd
    @0
    @10
    @5
    @6
    @7
    cA
    cxr
    @3
    eleq1a
    @0
    @6
    @10
    cA
    cA
    cle
    wbr
    #
    cA
    xrleid
    #
    @3
    cA
    cA
    cle
    breq2
    syl5ibrcom
    @0
    @7
    @10
    @16
    @17
    @3
    cA
    cA
    cle
    breq1
    syl5ibrcom
    3jcad
    impbid
    vx
    cA
    velsn
    syl6bbr
    bitrd
    eqrdv
end
