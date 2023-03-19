include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "nbgrisvtx.mm"
include "ssriv.mm"

theorem nbgrssvtx
  let cG: class G
  let cK: class K
  let cV: class V
  let ve: setvar e
  let cN: class N
  let vn: setvar n
  assume nbgrisvtx.v: |- V = ( Vtx ` G )


  assert |- ( G NeighbVtx K ) C_ V

  proof
    vn
    cG
    cK
    cnbgr
    co
    cV
    cG
    cK
    vn
    cv
    cV
    nbgrisvtx.v
    nbgrisvtx
    ssriv
end
