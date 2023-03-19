include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "scaffval.mm"
include "ovex.mm"
include "fnmpt2i.mm"

theorem scaffn
  let cB: class B
  let c.xb: class .xb
  let cF: class F
  let cK: class K
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume scaffval.b: |- B = ( Base ` W )
  assume scaffval.f: |- F = ( Scalar ` W )
  assume scaffval.k: |- K = ( Base ` F )
  assume scaffval.a: |- .xb = ( .sf ` W )


  assert |- .xb Fn ( K X. B )

  proof
    vx
    vy
    cK
    cB
    vx
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    c.xb
    vx
    vy
    cB
    c.xb
    @2
    cF
    cK
    cW
    scaffval.b
    scaffval.f
    scaffval.k
    scaffval.a
    @2
    eqid
    scaffval
    @0
    @1
    @2
    ovex
    fnmpt2i
end
