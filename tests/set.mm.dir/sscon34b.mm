include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "sscon.mm"
include "wceq.mm"
include "dfss4.mm"
include "biimpi.mm"
include "adantr.mm"
include "adantl.mm"
include "sseq12d.mm"
include "syl5ib.mm"
include "impbid2.mm"

theorem sscon34b
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ C /\ B C_ C ) -> ( A C_ B <-> ( C \ B ) C_ ( C \ A ) ) )

  proof
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wa
    #
    cA
    cB
    wss
    #
    cC
    cB
    cdif
    #
    cC
    cA
    cdif
    #
    wss
    #
    cA
    cB
    cC
    sscon
    @6
    cC
    @5
    cdif
    #
    cC
    @4
    cdif
    #
    wss
    @2
    @3
    @4
    @5
    cC
    sscon
    @2
    @7
    cA
    @8
    cB
    @0
    @7
    cA
    wceq
    #
    @1
    @0
    @9
    cA
    cC
    dfss4
    biimpi
    adantr
    @1
    @8
    cB
    wceq
    #
    @0
    @1
    @10
    cB
    cC
    dfss4
    biimpi
    adantl
    sseq12d
    syl5ib
    impbid2
end
