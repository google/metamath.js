include "cphl.mm"
include "wcel.mm"
include "cv.mm"
include "cip.mm"
include "cfv.mm"
include "co.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "eqid.mm"
include "ipcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "ipffval.mm"
include "fmpt2.mm"
include "sylib.mm"

theorem phlipf
  let cS: class S
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume ipffn.1: |- V = ( Base ` W )
  assume ipffn.2: |- ., = ( .if ` W )
  assume phlipf.s: |- S = ( Scalar ` W )
  assume phlipf.k: |- K = ( Base ` S )


  assert |- ( W e. PreHil -> ., : ( V X. V ) --> K )

  proof
    cW
    cphl
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cip
    cfv
    #
    co
    #
    cK
    wcel
    #
    vy
    cV
    wral
    vx
    cV
    wral
    cV
    cV
    cxp
    cK
    c.xi
    wf
    @0
    @5
    vx
    vy
    cV
    cV
    @0
    @1
    cV
    wcel
    @2
    cV
    wcel
    @5
    @1
    @2
    cS
    @3
    cK
    cV
    cW
    phlipf.s
    @3
    eqid
    #
    ipffn.1
    phlipf.k
    ipcl
    3expb
    ralrimivva
    vx
    vy
    cV
    cV
    @4
    cK
    c.xi
    vx
    vy
    c.xi
    @3
    cV
    cW
    ipffn.1
    @6
    ipffn.2
    ipffval
    fmpt2
    sylib
end
