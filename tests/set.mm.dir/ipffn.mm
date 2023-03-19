include "cv.mm"
include "cip.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "ipffval.mm"
include "ovex.mm"
include "fnmpt2i.mm"

theorem ipffn
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  assume ipffn.1: |- V = ( Base ` W )
  assume ipffn.2: |- ., = ( .if ` W )


  assert |- ., Fn ( V X. V )

  proof
    vx
    vy
    cV
    cV
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
    c.xi
    vx
    vy
    c.xi
    @2
    cV
    cW
    ipffn.1
    @2
    eqid
    ipffn.2
    ipffval
    @0
    @1
    @2
    ovex
    fnmpt2i
end
