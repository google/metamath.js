include "cngp.mm"
include "wcel.mm"
include "cmt.mm"
include "ctps.mm"
include "ngpms.mm"
include "mstps.mm"
include "syl.mm"

theorem ngptps
  let cG: class G


  assert |- ( G e. NrmGrp -> G e. TopSp )

  proof
    cG
    cngp
    wcel
    cG
    cmt
    wcel
    cG
    ctps
    wcel
    cG
    ngpms
    cG
    mstps
    syl
end
