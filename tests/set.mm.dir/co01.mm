include "c0.mm"
include "ccnv.mm"
include "ccom.mm"
include "cnv0.mm"
include "cnvco.mm"
include "coeq2i.mm"
include "co02.mm"
include "3eqtri.mm"
include "eqtr4i.mm"
include "cnveqi.mm"
include "wrel.mm"
include "wceq.mm"
include "rel0.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "relco.mm"
include "3eqtr3ri.mm"

theorem co01
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( (/) o. A ) = (/)

  proof
    c0
    ccnv
    #
    ccnv
    #
    c0
    cA
    ccom
    #
    ccnv
    #
    ccnv
    #
    c0
    @2
    @0
    @3
    @0
    c0
    @3
    cnv0
    @3
    cA
    ccnv
    #
    @0
    ccom
    @5
    c0
    ccom
    c0
    c0
    cA
    cnvco
    @0
    c0
    @5
    cnv0
    coeq2i
    @5
    co02
    3eqtri
    eqtr4i
    cnveqi
    c0
    wrel
    @1
    c0
    wceq
    rel0
    c0
    dfrel2
    mpbi
    @2
    wrel
    @4
    @2
    wceq
    c0
    cA
    relco
    @2
    dfrel2
    mpbi
    3eqtr3ri
end
