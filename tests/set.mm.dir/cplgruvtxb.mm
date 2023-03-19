include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cvtx.mm"
include "wceq.mm"
include "ccplgr.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqeq12d.mm"
include "df-cplgr.mm"
include "elab2g.mm"

theorem cplgruvtxb
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  assume cplgruvtxb.v: |- V = ( Vtx ` G )


  assert |- ( G e. W -> ( G e. ComplGraph <-> ( UnivVtx ` G ) = V ) )

  proof
    vg
    cv
    #
    cuvtx
    cfv
    #
    @0
    cvtx
    cfv
    #
    wceq
    cG
    cuvtx
    cfv
    #
    cV
    wceq
    vg
    cG
    ccplgr
    cW
    @0
    cG
    wceq
    #
    @1
    @3
    @2
    cV
    @0
    cG
    cuvtx
    fveq2
    @4
    @2
    cG
    cvtx
    cfv
    cV
    @0
    cG
    cvtx
    fveq2
    cplgruvtxb.v
    syl6eqr
    eqeq12d
    vg
    df-cplgr
    elab2g
end
