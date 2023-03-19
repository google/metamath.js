include "ccnv.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cnvin.mm"
include "cnveqi.mm"
include "wss.mm"
include "wceq.mm"
include "wrel.mm"
include "relcnv.mm"
include "df-rel.mm"
include "mpbi.mm"
include "relxp.mm"
include "dfrel2.mm"
include "sseqtr4i.mm"
include "dfss.mm"
include "3eqtr4ri.mm"
include "inss2.mm"
include "mpbir.mm"
include "eqtri.mm"

theorem cnvcnv
  let cA: class A


  assert |- `' `' A = ( A i^i ( _V X. _V ) )

  proof
    cA
    ccnv
    #
    ccnv
    #
    cA
    cvv
    cvv
    cxp
    #
    cin
    #
    ccnv
    #
    ccnv
    #
    @3
    @0
    @2
    ccnv
    #
    cin
    #
    ccnv
    @1
    @6
    ccnv
    #
    cin
    #
    @5
    @1
    @0
    @6
    cnvin
    @4
    @7
    cA
    @2
    cnvin
    cnveqi
    @1
    @8
    wss
    @1
    @9
    wceq
    @1
    @2
    @8
    @1
    wrel
    @1
    @2
    wss
    @0
    relcnv
    @1
    df-rel
    mpbi
    @2
    wrel
    @8
    @2
    wceq
    cvv
    cvv
    relxp
    @2
    dfrel2
    mpbi
    sseqtr4i
    @1
    @8
    dfss
    mpbi
    3eqtr4ri
    @3
    wrel
    #
    @5
    @3
    wceq
    @10
    @3
    @2
    wss
    cA
    @2
    inss2
    @3
    df-rel
    mpbir
    @3
    dfrel2
    mpbi
    eqtri
end
