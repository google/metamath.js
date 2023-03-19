include "wcel.mm"
include "ccplgr.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "cplgruvtxb.mm"
include "wss.mm"
include "wa.mm"
include "eqss.mm"
include "uvtxssvtx.mm"
include "dfss3.mm"
include "anbi2i.mm"
include "mpbiran.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem iscplgr
  let vv: setvar v
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  assume cplgruvtxb.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  disjoint G g
  disjoint V g
  disjoint g v
  assert |- ( G e. W -> ( G e. ComplGraph <-> A. v e. V v e. ( UnivVtx ` G ) ) )

  proof
    cG
    cW
    wcel
    cG
    ccplgr
    wcel
    cG
    cuvtx
    cfv
    #
    cV
    wceq
    #
    vv
    cv
    @0
    wcel
    vv
    cV
    wral
    #
    cG
    cV
    cW
    cplgruvtxb.v
    cplgruvtxb
    @1
    @0
    cV
    wss
    #
    cV
    @0
    wss
    #
    wa
    #
    @2
    @0
    cV
    eqss
    @5
    @3
    @2
    cG
    cV
    cplgruvtxb.v
    uvtxssvtx
    @4
    @2
    @3
    vv
    cV
    @0
    dfss3
    anbi2i
    mpbiran
    bitri
    syl6bb
end
