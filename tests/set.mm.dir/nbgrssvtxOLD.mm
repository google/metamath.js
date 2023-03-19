include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "nbgrisvtxOLD.mm"
include "ex.mm"
include "ssrdv.mm"

theorem nbgrssvtxOLD
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let ve: setvar e
  let cK: class K
  let vn: setvar n
  assume nbgrisvtx.v: |- V = ( Vtx ` G )


  assert |- ( G e. W -> ( G NeighbVtx N ) C_ V )

  proof
    cG
    cW
    wcel
    #
    vn
    cG
    cN
    cnbgr
    co
    #
    cV
    @0
    vn
    cv
    #
    @1
    wcel
    @2
    cV
    wcel
    cG
    cN
    @2
    cV
    cW
    nbgrisvtx.v
    nbgrisvtxOLD
    ex
    ssrdv
end
