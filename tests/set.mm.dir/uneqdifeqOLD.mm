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
include "difss.mm"
include "sseq1.mm"
include "unss.mm"
include "biimpi.mm"
include "syl6bi.mm"
include "mpi.mm"
include "adantr.mm"
include "imp.mm"
include "eqimss.mm"
include "ssundif.mm"
include "sylibr.mm"
include "adantlr.mm"
include "eqssd.mm"
include "ex.mm"
include "impbid.mm"

theorem uneqdifeqOLD
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
    #
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
    @5
    @7
    wi
    @0
    @5
    @2
    @7
    cB
    cA
    cun
    #
    @4
    wceq
    #
    @5
    @2
    @7
    wi
    #
    cB
    cA
    uncom
    @9
    @5
    wa
    #
    cC
    @8
    wceq
    #
    @10
    @11
    @8
    cC
    @8
    @4
    cC
    eqtr
    eqcomd
    @12
    @6
    @8
    cA
    cdif
    #
    wceq
    #
    @13
    cB
    cA
    cdif
    #
    wceq
    #
    @10
    cC
    @8
    cA
    difeq1
    cB
    cA
    difun2
    @14
    @16
    wa
    @6
    @15
    wceq
    #
    @2
    @7
    @6
    @13
    @15
    eqtr
    @2
    cB
    @15
    wceq
    #
    @17
    @7
    wi
    #
    @2
    cB
    cA
    cin
    #
    c0
    wceq
    @18
    @1
    @20
    c0
    cA
    cB
    incom
    eqeq1i
    cB
    cA
    disj3
    bitri
    @19
    @15
    cB
    @17
    @15
    cB
    wceq
    @7
    @6
    @15
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
    @3
    @7
    @5
    @3
    @7
    wa
    @4
    cC
    @3
    @7
    @4
    cC
    wss
    #
    @0
    @7
    @21
    wi
    @2
    @7
    @0
    @21
    @7
    @6
    cC
    wss
    #
    @0
    @21
    wi
    #
    cC
    cA
    difss
    @7
    @22
    cB
    cC
    wss
    #
    @23
    @6
    cB
    cC
    sseq1
    @0
    @24
    @21
    @0
    @24
    wa
    @21
    cA
    cB
    cC
    unss
    biimpi
    expcom
    syl6bi
    mpi
    com12
    adantr
    imp
    @0
    @7
    cC
    @4
    wss
    #
    @2
    @0
    @7
    wa
    @6
    cB
    wss
    #
    @25
    @7
    @26
    @0
    @6
    cB
    eqimss
    adantl
    cC
    cA
    cB
    ssundif
    sylibr
    adantlr
    eqssd
    ex
    impbid
end
