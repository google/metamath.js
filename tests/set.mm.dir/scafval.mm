include "cv.mm"
include "co.mm"
include "oveq12.mm"
include "scaffval.mm"
include "ovex.mm"
include "ovmpt2a.mm"

theorem scafval
  let cB: class B
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume scaffval.b: |- B = ( Base ` W )
  assume scaffval.f: |- F = ( Scalar ` W )
  assume scaffval.k: |- K = ( Base ` F )
  assume scaffval.a: |- .xb = ( .sf ` W )
  assume scaffval.s: |- .x. = ( .s ` W )


  assert |- ( ( X e. K /\ Y e. B ) -> ( X .xb Y ) = ( X .x. Y ) )

  proof
    vx
    vy
    cX
    cY
    cK
    cB
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    cX
    cY
    c.x
    co
    c.xb
    @0
    cX
    @1
    cY
    c.x
    oveq12
    vx
    vy
    cB
    c.xb
    c.x
    cF
    cK
    cW
    scaffval.b
    scaffval.f
    scaffval.k
    scaffval.a
    scaffval.s
    scaffval
    cX
    cY
    c.x
    ovex
    ovmpt2a
end
