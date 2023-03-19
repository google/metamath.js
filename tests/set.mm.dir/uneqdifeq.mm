include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "cdif.mm"
include "wi.mm"
include "uncom.mm"
include "eqtr.mm"
include "eqcomd.mm"
include "difeq1.mm"
include "difun2.mm"
include "incom.mm"
include "eqeq1i.mm"
include "disj3.mm"
include "bitri.mm"
include "expcom.mm"
include "eqcoms.mm"
include "sylbi.mm"
include "syl5com.mm"
include "sylancl.mm"
include "syl.mm"
include "mpan.mm"
include "com12.mm"
include "adantl.mm"
include "simpl.mm"
include "difssd.mm"
include "sseq1.mm"
include "mpbid.mm"
include "unssd.mm"
include "eqimss.mm"
include "ssundif.mm"
include "sylibr.mm"
include "eqssd.mm"
include "ex.mm"
include "adantr.mm"
include "impbid.mm"

theorem uneqdifeq
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ C /\ ( A i^i B ) = (/) ) -> ( ( A u. B ) = C <-> ( C \ A ) = B ) )

  proof
    cA
    cC
    wss
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    wa
    cA
    cB
    cun
    #
    cC
    wceq
    #
    cC
    cA
    cdif
    #
    cB
    wceq
    #
    @2
    @4
    @6
    wi
    @0
    @4
    @2
    @6
    cB
    cA
    cun
    #
    @3
    wceq
    #
    @4
    @2
    @6
    wi
    #
    cB
    cA
    uncom
    @8
    @4
    wa
    #
    cC
    @7
    wceq
    #
    @9
    @10
    @7
    cC
    @7
    @3
    cC
    eqtr
    eqcomd
    @11
    @5
    @7
    cA
    cdif
    #
    wceq
    #
    @12
    cB
    cA
    cdif
    #
    wceq
    #
    @9
    cC
    @7
    cA
    difeq1
    cB
    cA
    difun2
    @13
    @15
    wa
    @5
    @14
    wceq
    #
    @2
    @6
    @5
    @12
    @14
    eqtr
    @2
    cB
    @14
    wceq
    #
    @16
    @6
    wi
    #
    @2
    cB
    cA
    cin
    #
    c0
    wceq
    @17
    @1
    @19
    c0
    cA
    cB
    incom
    eqeq1i
    cB
    cA
    disj3
    bitri
    @18
    @14
    cB
    @16
    @14
    cB
    wceq
    @6
    @5
    @14
    cB
    eqtr
    expcom
    eqcoms
    sylbi
    syl5com
    sylancl
    syl
    mpan
    com12
    adantl
    @0
    @6
    @4
    wi
    @2
    @0
    @6
    @4
    @0
    @6
    wa
    #
    @3
    cC
    @20
    cA
    cB
    cC
    @0
    @6
    simpl
    @6
    cB
    cC
    wss
    #
    @0
    @6
    @5
    cC
    wss
    @21
    @6
    cC
    cA
    difssd
    @5
    cB
    cC
    sseq1
    mpbid
    adantl
    unssd
    @6
    cC
    @3
    wss
    #
    @0
    @6
    @5
    cB
    wss
    @22
    @5
    cB
    eqimss
    cC
    cA
    cB
    ssundif
    sylibr
    adantl
    eqssd
    ex
    adantr
    impbid
end
