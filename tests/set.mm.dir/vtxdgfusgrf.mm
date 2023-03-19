include "cfusgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cfn.mm"
include "cn0.mm"
include "cvtxdg.mm"
include "wf.mm"
include "cedg.mm"
include "fusgrfis.mm"
include "cusgr.mm"
include "wb.mm"
include "fusgrusgr.mm"
include "eqid.mm"
include "usgredgffibi.mm"
include "syl.mm"
include "wfun.mm"
include "usgrfun.mm"
include "fundmfibi.mm"
include "3syl.mm"
include "bitrd.mm"
include "mpbid.mm"
include "vtxdgfisf.mm"
include "mpdan.mm"

theorem vtxdgfusgrf
  let cG: class G
  let cV: class V
  assume vtxdgfusgrf.v: |- V = ( Vtx ` G )


  assert |- ( G e. FinUSGraph -> ( VtxDeg ` G ) : V --> NN0 )

  proof
    cG
    cfusgr
    wcel
    #
    cG
    ciedg
    cfv
    #
    cdm
    #
    cfn
    wcel
    #
    cV
    cn0
    cG
    cvtxdg
    cfv
    wf
    @0
    cG
    cedg
    cfv
    #
    cfn
    wcel
    #
    @3
    cG
    fusgrfis
    @0
    @5
    @1
    cfn
    wcel
    #
    @3
    @0
    cG
    cusgr
    wcel
    #
    @5
    @6
    wb
    cG
    fusgrusgr
    #
    @4
    cG
    @1
    @1
    eqid
    #
    @4
    eqid
    usgredgffibi
    syl
    @0
    @7
    @1
    wfun
    @6
    @3
    wb
    @8
    cG
    usgrfun
    @1
    fundmfibi
    3syl
    bitrd
    mpbid
    @2
    cG
    @1
    cV
    cfusgr
    vtxdgfusgrf.v
    @9
    @2
    eqid
    vtxdgfisf
    mpdan
end
