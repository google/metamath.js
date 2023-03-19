include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "clt.mm"
include "w3o.mm"
include "elicc1.mm"
include "wi.mm"
include "simp1.mm"
include "a1i.mm"
include "xrletr.mm"
include "exp5o.mm"
include "com23.mm"
include "imp5q.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "xrleltne.mm"
include "biimprd.mm"
include "syl5bir.mm"
include "3adant3r3.mm"
include "adantlr.mm"
include "eqcom.mm"
include "necon3bbii.mm"
include "syl5bi.mm"
include "3exp.mm"
include "com12.mm"
include "imp32.mm"
include "3adantr2.mm"
include "adantll.mm"
include "anim12d.mm"
include "ex.mm"
include "wo.mm"
include "df-or.mm"
include "3orass.mm"
include "pm5.6.mm"
include "orcom.mm"
include "imbi2i.mm"
include "bitri.mm"
include "3bitr4ri.mm"
include "syl6ib.mm"
include "3jcad.mm"
include "xrleid.mm"
include "ad3antrrr.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "xrltle.mm"
include "adantr.mm"
include "adantllr.mm"
include "adantrd.mm"
include "simpr.mm"
include "3jaod.mm"
include "exp31.mm"
include "3impd.mm"
include "breq1.mm"
include "ancoms.mm"
include "adantld.mm"
include "ad3antlr.mm"
include "impbid.mm"
include "bitrd.mm"

theorem elicc3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( C e. ( A [,] B ) <-> ( C e. RR* /\ A <_ B /\ ( C = A \/ ( A < C /\ C < B ) \/ C = B ) ) ) )

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
    cC
    cA
    cB
    cicc
    co
    wcel
    cC
    cxr
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    w3a
    #
    @3
    cA
    cB
    cle
    wbr
    #
    cC
    cA
    wceq
    #
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    wa
    #
    cC
    cB
    wceq
    #
    w3o
    #
    w3a
    #
    cA
    cB
    cC
    elicc1
    @2
    @6
    @14
    @2
    @6
    @3
    @7
    @13
    @6
    @3
    wi
    @2
    @3
    @4
    @5
    simp1
    a1i
    @0
    @1
    @3
    @4
    @5
    @7
    @0
    @3
    @1
    @4
    @5
    @7
    wi
    wi
    @0
    @3
    @1
    @4
    @5
    @7
    cA
    cC
    cB
    xrletr
    exp5o
    com23
    imp5q
    @2
    @6
    @8
    wn
    #
    @12
    wn
    #
    wa
    @11
    wi
    #
    @13
    @2
    @6
    @17
    @2
    @6
    wa
    @15
    @9
    @16
    @10
    @0
    @6
    @15
    @9
    wi
    #
    @1
    @0
    @3
    @4
    @18
    @5
    @15
    cC
    cA
    wne
    #
    @0
    @3
    @4
    w3a
    #
    @9
    cC
    cA
    df-ne
    @20
    @9
    @19
    cA
    cC
    xrleltne
    biimprd
    syl5bir
    3adant3r3
    adantlr
    @1
    @6
    @16
    @10
    wi
    #
    @0
    @1
    @3
    @5
    @21
    @4
    @1
    @3
    @5
    @21
    @3
    @1
    @5
    @21
    wi
    @3
    @1
    @5
    @21
    @16
    cB
    cC
    wne
    #
    @3
    @1
    @5
    w3a
    #
    @10
    @12
    cB
    cC
    cC
    cB
    eqcom
    necon3bbii
    @23
    @10
    @22
    cC
    cB
    xrleltne
    biimprd
    syl5bi
    3exp
    com12
    imp32
    3adantr2
    adantll
    anim12d
    ex
    @8
    @11
    @12
    wo
    #
    wo
    @15
    @24
    wi
    #
    @13
    @17
    @8
    @24
    df-or
    @8
    @11
    @12
    3orass
    @17
    @15
    @12
    @11
    wo
    #
    wi
    @25
    @15
    @12
    @11
    pm5.6
    @26
    @24
    @15
    @12
    @11
    orcom
    imbi2i
    bitri
    3bitr4ri
    syl6ib
    3jcad
    @2
    @14
    @3
    @4
    @5
    @14
    @3
    wi
    @2
    @3
    @7
    @13
    simp1
    a1i
    @2
    @3
    @7
    @13
    @4
    @2
    @3
    @7
    @13
    @4
    wi
    @2
    @3
    wa
    #
    @7
    wa
    #
    @8
    @4
    @11
    @12
    @28
    @4
    @8
    cA
    cA
    cle
    wbr
    #
    @0
    @29
    @1
    @3
    @7
    cA
    xrleid
    ad3antrrr
    cC
    cA
    cA
    cle
    breq2
    syl5ibrcom
    @28
    @9
    @4
    @10
    @0
    @3
    @7
    @9
    @4
    wi
    #
    @1
    @0
    @3
    wa
    @30
    @7
    cA
    cC
    xrltle
    adantr
    adantllr
    adantrd
    @28
    @4
    @12
    @7
    @27
    @7
    simpr
    #
    cC
    cB
    cA
    cle
    breq2
    syl5ibrcom
    3jaod
    exp31
    3impd
    @2
    @3
    @7
    @13
    @5
    @2
    @3
    @7
    @13
    @5
    wi
    @28
    @8
    @5
    @11
    @12
    @28
    @5
    @8
    @7
    @31
    cC
    cA
    cB
    cle
    breq1
    syl5ibrcom
    @27
    @11
    @5
    wi
    #
    @7
    @1
    @3
    @32
    @0
    @1
    @3
    wa
    @10
    @5
    @9
    @3
    @1
    @10
    @5
    wi
    cC
    cB
    xrltle
    ancoms
    adantld
    adantll
    adantr
    @28
    @5
    @12
    cB
    cB
    cle
    wbr
    #
    @1
    @33
    @0
    @3
    @7
    cB
    xrleid
    ad3antlr
    cC
    cB
    cB
    cle
    breq1
    syl5ibrcom
    3jaod
    exp31
    3impd
    3jcad
    impbid
    bitrd
end
