include "wcel.mm"
include "ccom.mm"
include "ctcl.mm"
include "cfv.mm"
include "trclfvlb.mm"
include "trclfvlb2.mm"
include "unssd.mm"

theorem trclfvlb3
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R u. ( R o. R ) ) C_ ( t+ ` R ) )

  proof
    cR
    cV
    wcel
    cR
    cR
    cR
    ccom
    cR
    ctcl
    cfv
    cR
    cV
    trclfvlb
    cR
    cV
    trclfvlb2
    unssd
end
