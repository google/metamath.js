include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "fnov.mm"
include "biimpi.mm"
include "ipffval.mm"
include "syl6reqr.mm"

theorem ipfeq
  let c.x: class .x.
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume ipffval.1: |- V = ( Base ` W )
  assume ipffval.2: |- ., = ( .i ` W )
  assume ipffval.3: |- .x. = ( .if ` W )


  assert |- ( ., Fn ( V X. V ) -> .x. = ., )

  proof
    c.xi
    cV
    cV
    cxp
    wfn
    #
    c.xi
    vx
    vy
    cV
    cV
    vx
    cv
    vy
    cv
    c.xi
    co
    cmpt2
    #
    c.x
    @0
    c.xi
    @1
    wceq
    vx
    vy
    cV
    cV
    c.xi
    fnov
    biimpi
    vx
    vy
    c.x
    c.xi
    cV
    cW
    ipffval.1
    ipffval.2
    ipffval.3
    ipffval
    syl6reqr
end
