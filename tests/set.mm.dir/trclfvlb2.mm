include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "trclfvcotr.mm"
include "trclfvlb.mm"
include "trrelssd.mm"

theorem trclfvlb2
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R o. R ) C_ ( t+ ` R ) )

  proof
    cR
    cV
    wcel
    cR
    ctcl
    cfv
    cR
    cR
    cR
    cV
    trclfvcotr
    cR
    cV
    trclfvlb
    #
    @0
    trrelssd
end
