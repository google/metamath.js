include "cuvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wss.mm"
include "vtxnbuvtx.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem uvtxnbgrss
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  assume uvtxel.v: |- V = ( Vtx ` G )


  assert |- ( N e. ( UnivVtx ` G ) -> ( V \ { N } ) C_ ( G NeighbVtx N ) )

  proof
    cN
    cG
    cuvtx
    cfv
    wcel
    vn
    cv
    cG
    cN
    cnbgr
    co
    #
    wcel
    vn
    cV
    cN
    csn
    cdif
    #
    wral
    @1
    @0
    wss
    vn
    cG
    cN
    cV
    uvtxel.v
    vtxnbuvtx
    vn
    @1
    @0
    dfss3
    sylibr
end
