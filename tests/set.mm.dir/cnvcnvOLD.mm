include "ccnv.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
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
include "cnvin.mm"
include "cnveqi.mm"
include "inss2.mm"
include "mpbir.mm"
include "eqtr3i.mm"
include "3eqtr2i.mm"

theorem cnvcnvOLD
  let cA: class A


  assert |- `' `' A = ( A i^i ( _V X. _V ) )

  proof
    cA
    ccnv
    #
    ccnv
    #
    @1
    cvv
    cvv
    cxp
    #
    ccnv
    #
    ccnv
    #
    cin
    #
    @0
    @3
    cin
    #
    ccnv
    #
    cA
    @2
    cin
    #
    @1
    @4
    wss
    @1
    @5
    wceq
    @1
    @2
    @4
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
    @4
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
    @4
    dfss
    mpbi
    @0
    @3
    cnvin
    @8
    ccnv
    #
    ccnv
    #
    @7
    @8
    @9
    @6
    cA
    @2
    cnvin
    cnveqi
    @8
    wrel
    #
    @10
    @8
    wceq
    @11
    @8
    @2
    wss
    cA
    @2
    inss2
    @8
    df-rel
    mpbir
    @8
    dfrel2
    mpbi
    eqtr3i
    3eqtr2i
end
