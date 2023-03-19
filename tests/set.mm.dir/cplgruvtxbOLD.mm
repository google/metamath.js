include "wcel.mm"
include "ccplgr.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wral.mm"
include "wceq.mm"
include "iscplgr.mm"
include "wa.mm"
include "wss.mm"
include "uvtxisvtx.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "adantr.mm"
include "biimpri.mm"
include "eqssd.mm"
include "ex.mm"
include "raleleq.mm"
include "eqcoms.mm"
include "impbid1.mm"
include "bitrd.mm"

theorem cplgruvtxbOLD
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vv: setvar v
  assume cplgruvtxb.v: |- V = ( Vtx ` G )


  assert |- ( G e. W -> ( G e. ComplGraph <-> ( UnivVtx ` G ) = V ) )

  proof
    cG
    cW
    wcel
    #
    cG
    ccplgr
    wcel
    vv
    cv
    cG
    cuvtx
    cfv
    #
    wcel
    vv
    cV
    wral
    #
    @1
    cV
    wceq
    #
    vv
    cG
    cV
    cW
    cplgruvtxb.v
    iscplgr
    @0
    @2
    @3
    @0
    @2
    @3
    @0
    @2
    wa
    @1
    cV
    @0
    @1
    cV
    wss
    #
    @2
    @0
    vg
    cv
    #
    cV
    wcel
    #
    vg
    @1
    wral
    @4
    @0
    @6
    vg
    @1
    @5
    @1
    wcel
    @6
    @0
    cG
    @5
    cV
    cplgruvtxb.v
    uvtxisvtx
    adantl
    ralrimiva
    vg
    @1
    cV
    dfss3
    sylibr
    adantr
    @2
    cV
    @1
    wss
    #
    @0
    @7
    @2
    vv
    cV
    @1
    dfss3
    biimpri
    adantl
    eqssd
    ex
    @2
    cV
    @1
    vv
    cV
    @1
    raleleq
    eqcoms
    impbid1
    bitrd
end
