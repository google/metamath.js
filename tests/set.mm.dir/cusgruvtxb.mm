include "ccusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "wa.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "iscusgr.mm"
include "ibar.mm"
include "cplgruvtxb.mm"
include "bitr3d.mm"
include "syl5bb.mm"

theorem cusgruvtxb
  let cG: class G
  let cV: class V
  let vv: setvar v
  assume iscusgrvtx.v: |- V = ( Vtx ` G )


  assert |- ( G e. USGraph -> ( G e. ComplUSGraph <-> ( UnivVtx ` G ) = V ) )

  proof
    cG
    ccusgr
    wcel
    cG
    cusgr
    wcel
    #
    cG
    ccplgr
    wcel
    #
    wa
    #
    @0
    cG
    cuvtx
    cfv
    cV
    wceq
    #
    cG
    iscusgr
    @0
    @1
    @2
    @3
    @0
    @1
    ibar
    cG
    cV
    cusgr
    iscusgrvtx.v
    cplgruvtxb
    bitr3d
    syl5bb
end
