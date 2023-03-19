include "cngp.mm"
include "wcel.mm"
include "cmt.mm"
include "cxme.mm"
include "ngpms.mm"
include "msxms.mm"
include "syl.mm"

theorem ngpxms
  let cG: class G


  assert |- ( G e. NrmGrp -> G e. *MetSp )

  proof
    cG
    cngp
    wcel
    cG
    cmt
    wcel
    cG
    cxme
    wcel
    cG
    ngpms
    cG
    msxms
    syl
end
