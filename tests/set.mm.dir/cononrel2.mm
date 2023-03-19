include "ccnv.mm"
include "cdif.mm"
include "ccom.mm"
include "c0.mm"
include "cnvco.mm"
include "cnvnonrel.mm"
include "coeq1i.mm"
include "co01.mm"
include "3eqtri.mm"
include "cnveqi.mm"
include "wrel.mm"
include "wceq.mm"
include "relco.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "cnv0.mm"
include "3eqtr3i.mm"

theorem cononrel2
  let cA: class A
  let cB: class B


  assert |- ( A o. ( B \ `' `' B ) ) = (/)

  proof
    cA
    cB
    cB
    ccnv
    ccnv
    cdif
    #
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
    @0
    ccnv
    #
    cA
    ccnv
    #
    ccom
    c0
    @5
    ccom
    c0
    cA
    @0
    cnvco
    @4
    c0
    @5
    cB
    cnvnonrel
    coeq1i
    @5
    co01
    3eqtri
    cnveqi
    @1
    wrel
    @3
    @1
    wceq
    cA
    @0
    relco
    @1
    dfrel2
    mpbi
    cnv0
    3eqtr3i
end
