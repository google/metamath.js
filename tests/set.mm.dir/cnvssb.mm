include "wrel.mm"
include "wss.mm"
include "ccnv.mm"
include "cnvss.mm"
include "wa.mm"
include "wceq.mm"
include "dfrel2.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "adantr.mm"
include "id.mm"
include "cnvcnvss.mm"
include "syl6ss.mm"
include "adantl.mm"
include "eqsstrd.mm"
include "ex.mm"
include "syl5.mm"
include "impbid2.mm"

theorem cnvssb
  let cA: class A
  let cB: class B


  assert |- ( Rel A -> ( A C_ B <-> `' A C_ `' B ) )

  proof
    cA
    wrel
    #
    cA
    cB
    wss
    #
    cA
    ccnv
    #
    cB
    ccnv
    #
    wss
    #
    cA
    cB
    cnvss
    @4
    @2
    ccnv
    #
    @3
    ccnv
    #
    wss
    #
    @0
    @1
    @2
    @3
    cnvss
    @0
    @7
    @1
    @0
    @7
    wa
    cA
    @5
    cB
    @0
    cA
    @5
    wceq
    @7
    @0
    @5
    cA
    @0
    @5
    cA
    wceq
    cA
    dfrel2
    biimpi
    eqcomd
    adantr
    @7
    @5
    cB
    wss
    @0
    @7
    @5
    @6
    cB
    @7
    id
    cB
    cnvcnvss
    syl6ss
    adantl
    eqsstrd
    ex
    syl5
    impbid2
end
