include "cuvtx.mm"
include "cfv.mm"
include "cv.mm"
include "uvtxisvtx.mm"
include "ssriv.mm"

theorem uvtxssvtx
  let cG: class G
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  let cN: class N
  assume uvtxel.v: |- V = ( Vtx ` G )


  assert |- ( UnivVtx ` G ) C_ V

  proof
    vn
    cG
    cuvtx
    cfv
    cV
    cG
    vn
    cv
    cV
    uvtxel.v
    uvtxisvtx
    ssriv
end
