include "cv.mm"
include "co.mm"
include "oveq12.mm"
include "ipffval.mm"
include "ovex.mm"
include "ovmpt2a.mm"

theorem ipfval
  let c.x: class .x.
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume ipffval.1: |- V = ( Base ` W )
  assume ipffval.2: |- ., = ( .i ` W )
  assume ipffval.3: |- .x. = ( .if ` W )


  assert |- ( ( X e. V /\ Y e. V ) -> ( X .x. Y ) = ( X ., Y ) )

  proof
    vx
    vy
    cX
    cY
    cV
    cV
    vx
    cv
    #
    vy
    cv
    #
    c.xi
    co
    cX
    cY
    c.xi
    co
    c.x
    @0
    cX
    @1
    cY
    c.xi
    oveq12
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
    cX
    cY
    c.xi
    ovex
    ovmpt2a
end
