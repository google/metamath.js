include "ccnv.mm"
include "cdif.mm"
include "ccom.mm"
include "c0.mm"
include "cnvco.mm"
include "cnvnonrel.mm"
include "coeq2i.mm"
include "co02.mm"
include "3eqtri.mm"
include "cnveqi.mm"
include "wrel.mm"
include "wceq.mm"
include "relco.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "cnv0.mm"
include "3eqtr3i.mm"

theorem cononrel1
  let cA: class A
  let cB: class B


  assert |- ( ( A \ `' `' A ) o. B ) = (/)

  proof
    cA
    cA
    ccnv
    ccnv
    cdif
    #
    cB
    ccom
    #
    ccnv
    #
    ccnv
    #
    c0
    ccnv
    @1
    c0
    @2
    c0
    @2
    cB
    ccnv
    #
    @0
    ccnv
    #
    ccom
    @4
    c0
    ccom
    c0
    @0
    cB
    cnvco
    @5
    c0
    @4
    cA
    cnvnonrel
    coeq2i
    @4
    co02
    3eqtri
    cnveqi
    @1
    wrel
    @3
    @1
    wceq
    @0
    cB
    relco
    @1
    dfrel2
    mpbi
    cnv0
    3eqtr3i
end
