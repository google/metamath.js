include "cuvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "nbgrssovtx.mm"
include "a1i.mm"
include "uvtxnbgrss.mm"
include "eqssd.mm"

theorem uvtxnbgr
  let cG: class G
  let cN: class N
  let cV: class V
  assume uvtxnbgr.v: |- V = ( Vtx ` G )


  assert |- ( N e. ( UnivVtx ` G ) -> ( G NeighbVtx N ) = ( V \ { N } ) )

  proof
    cN
    cG
    cuvtx
    cfv
    wcel
    #
    cG
    cN
    cnbgr
    co
    #
    cV
    cN
    csn
    cdif
    #
    @1
    @2
    wss
    @0
    cG
    cV
    cN
    uvtxnbgr.v
    nbgrssovtx
    a1i
    cG
    cN
    cV
    uvtxnbgr.v
    uvtxnbgrss
    eqssd
end
