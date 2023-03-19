include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "ccom.mm"
include "cun.mm"
include "trclfvdecomr.mm"
include "trclfvcom.mm"
include "uneq2d.mm"
include "eqtrd.mm"

theorem trclfvdecoml
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( t+ ` R ) = ( R u. ( R o. ( t+ ` R ) ) ) )

  proof
    cR
    cV
    wcel
    #
    cR
    ctcl
    cfv
    #
    cR
    @1
    cR
    ccom
    #
    cun
    cR
    cR
    @1
    ccom
    #
    cun
    cR
    cV
    trclfvdecomr
    @0
    @2
    @3
    cR
    cR
    cV
    trclfvcom
    uneq2d
    eqtrd
end
