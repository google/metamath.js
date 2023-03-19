include "cuvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "uvtxel.mm"
include "simplbi.mm"

theorem uvtxisvtx
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  assume uvtxel.v: |- V = ( Vtx ` G )


  assert |- ( N e. ( UnivVtx ` G ) -> N e. V )

  proof
    cN
    cG
    cuvtx
    cfv
    wcel
    cN
    cV
    wcel
    vn
    cv
    cG
    cN
    cnbgr
    co
    wcel
    vn
    cV
    cN
    csn
    cdif
    wral
    vn
    cG
    cN
    cV
    uvtxel.v
    uvtxel
    simplbi
end
