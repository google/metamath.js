include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "wceq.mm"
include "cioo.mm"
include "w3o.mm"
include "wa.mm"
include "wo.mm"
include "cpr.mm"
include "cun.mm"
include "prunioo.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "wb.mm"
include "elun.mm"
include "elprg.mm"
include "orbi2d.mm"
include "syl5bb.mm"
include "adantl.mm"
include "mpbid.mm"
include "3orass.mm"
include "3orcoma.mm"
include "bitr3i.mm"
include "sylib.mm"
include "lbicc2.mm"
include "adantr.mm"
include "eleq1.mm"
include "mpbird.mm"
include "ioossicc.mm"
include "sseli.mm"
include "ubicc2.mm"
include "3jaodan.mm"
include "impbida.mm"

theorem eliccioo
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) -> ( C e. ( A [,] B ) <-> ( C = A \/ C e. ( A (,) B ) \/ C = B ) ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    w3a
    #
    cC
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cC
    cA
    wceq
    #
    cC
    cA
    cB
    cioo
    co
    #
    wcel
    #
    cC
    cB
    wceq
    #
    w3o
    #
    @0
    @2
    wa
    #
    @5
    @3
    @6
    wo
    #
    wo
    #
    @7
    @8
    cC
    @4
    cA
    cB
    cpr
    #
    cun
    #
    wcel
    #
    @10
    @0
    @13
    @2
    @0
    @12
    @1
    cC
    cA
    cB
    prunioo
    eleq2d
    biimpar
    @2
    @13
    @10
    wb
    @0
    @13
    @5
    cC
    @11
    wcel
    #
    wo
    @2
    @10
    cC
    @4
    @11
    elun
    @2
    @14
    @9
    @5
    cC
    cA
    cB
    @1
    elprg
    orbi2d
    syl5bb
    adantl
    mpbid
    @10
    @5
    @3
    @6
    w3o
    @7
    @5
    @3
    @6
    3orass
    @5
    @3
    @6
    3orcoma
    bitr3i
    sylib
    @0
    @3
    @2
    @5
    @6
    @0
    @3
    wa
    @2
    cA
    @1
    wcel
    #
    @0
    @15
    @3
    cA
    cB
    lbicc2
    adantr
    @3
    @2
    @15
    wb
    @0
    cC
    cA
    @1
    eleq1
    adantl
    mpbird
    @5
    @2
    @0
    @4
    @1
    cC
    cA
    cB
    ioossicc
    sseli
    adantl
    @0
    @6
    wa
    @2
    cB
    @1
    wcel
    #
    @0
    @16
    @6
    cA
    cB
    ubicc2
    adantr
    @6
    @2
    @16
    wb
    @0
    cC
    cB
    @1
    eleq1
    adantl
    mpbird
    3jaodan
    impbida
end
