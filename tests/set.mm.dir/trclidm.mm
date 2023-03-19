include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "cvv.mm"
include "ccom.mm"
include "wss.mm"
include "wceq.mm"
include "fvex.mm"
include "trclfvcotr.mm"
include "cotrtrclfv.mm"
include "sylancr.mm"

theorem trclidm
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( t+ ` ( t+ ` R ) ) = ( t+ ` R ) )

  proof
    cR
    cV
    wcel
    cR
    ctcl
    cfv
    #
    cvv
    wcel
    @0
    @0
    ccom
    @0
    wss
    @0
    ctcl
    cfv
    @0
    wceq
    cR
    ctcl
    fvex
    cR
    cV
    trclfvcotr
    @0
    cvv
    cotrtrclfv
    sylancr
end
