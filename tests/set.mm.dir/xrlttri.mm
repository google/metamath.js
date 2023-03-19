include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "xrltnr.mm"
include "adantr.mm"
include "wb.mm"
include "breq2.mm"
include "adantl.mm"
include "mtbid.mm"
include "ex.mm"
include "xrltnsym.mm"
include "ancoms.mm"
include "jaod.mm"
include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "w3o.mm"
include "elxr.mm"
include "axlttri.mm"
include "biimprd.mm"
include "con1d.mm"
include "ltpnf.mm"
include "mpbird.mm"
include "pm2.24d.mm"
include "mnflt.mm"
include "breq1.mm"
include "olcd.mm"
include "a1d.mm"
include "3jaodan.mm"
include "eqtr3.mm"
include "orcd.mm"
include "mnfltpnf.mm"
include "breq12.mm"
include "mpbiri.mm"
include "3jaoian.mm"
include "syl2anb.mm"
include "impbid.mm"
include "con2bid.mm"

theorem xrlttri
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B <-> -. ( A = B \/ B < A ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    #
    cB
    cA
    clt
    wbr
    #
    wo
    #
    cA
    cB
    clt
    wbr
    #
    @2
    @5
    @6
    wn
    #
    @2
    @3
    @7
    @4
    @0
    @3
    @7
    wi
    @1
    @0
    @3
    @7
    @0
    @3
    wa
    cA
    cA
    clt
    wbr
    #
    @6
    @0
    @8
    wn
    @3
    cA
    xrltnr
    adantr
    @3
    @8
    @6
    wb
    @0
    cA
    cB
    cA
    clt
    breq2
    adantl
    mtbid
    ex
    adantr
    @1
    @0
    @4
    @7
    wi
    cB
    cA
    xrltnsym
    ancoms
    jaod
    @0
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    cB
    cr
    wcel
    #
    cB
    cpnf
    wceq
    #
    cB
    cmnf
    wceq
    #
    w3o
    #
    @7
    @5
    wi
    #
    @1
    cA
    elxr
    cB
    elxr
    @9
    @15
    @16
    @10
    @11
    @9
    @12
    @16
    @13
    @14
    @9
    @12
    wa
    #
    @5
    @6
    @17
    @6
    @5
    wn
    cA
    cB
    axlttri
    biimprd
    con1d
    @9
    @13
    wa
    #
    @6
    @5
    @18
    @6
    cA
    cpnf
    clt
    wbr
    #
    @9
    @19
    @13
    cA
    ltpnf
    adantr
    @13
    @6
    @19
    wb
    @9
    cB
    cpnf
    cA
    clt
    breq2
    adantl
    mpbird
    pm2.24d
    @9
    @14
    wa
    #
    @5
    @7
    @20
    @4
    @3
    @20
    @4
    cmnf
    cA
    clt
    wbr
    #
    @9
    @21
    @14
    cA
    mnflt
    adantr
    @14
    @4
    @21
    wb
    @9
    cB
    cmnf
    cA
    clt
    breq1
    adantl
    mpbird
    olcd
    a1d
    3jaodan
    @10
    @12
    @16
    @13
    @14
    @10
    @12
    wa
    #
    @5
    @7
    @22
    @4
    @3
    @22
    @4
    cB
    cpnf
    clt
    wbr
    #
    @12
    @23
    @10
    cB
    ltpnf
    adantl
    @10
    @4
    @23
    wb
    @12
    cA
    cpnf
    cB
    clt
    breq2
    adantr
    mpbird
    olcd
    a1d
    @10
    @13
    wa
    #
    @5
    @7
    @24
    @3
    @4
    cA
    cB
    cpnf
    eqtr3
    orcd
    a1d
    @10
    @14
    wa
    #
    @5
    @7
    @25
    @4
    @3
    @14
    @10
    @4
    @14
    @10
    wa
    @4
    cmnf
    cpnf
    clt
    wbr
    #
    mnfltpnf
    cB
    cmnf
    cA
    cpnf
    clt
    breq12
    mpbiri
    ancoms
    olcd
    a1d
    3jaodan
    @11
    @12
    @16
    @13
    @14
    @11
    @12
    wa
    #
    @6
    @5
    @27
    @6
    cmnf
    cB
    clt
    wbr
    #
    @12
    @28
    @11
    cB
    mnflt
    adantl
    @11
    @6
    @28
    wb
    @12
    cA
    cmnf
    cB
    clt
    breq1
    adantr
    mpbird
    pm2.24d
    @11
    @13
    wa
    #
    @6
    @5
    @29
    @6
    @26
    mnfltpnf
    cA
    cmnf
    cB
    cpnf
    clt
    breq12
    mpbiri
    pm2.24d
    @11
    @14
    wa
    #
    @5
    @7
    @30
    @3
    @4
    cA
    cB
    cmnf
    eqtr3
    orcd
    a1d
    3jaodan
    3jaoian
    syl2anb
    impbid
    con2bid
end
