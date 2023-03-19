include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "fnov.mm"
include "biimpi.mm"
include "scaffval.mm"
include "syl6reqr.mm"

theorem scafeq
  let cB: class B
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume scaffval.b: |- B = ( Base ` W )
  assume scaffval.f: |- F = ( Scalar ` W )
  assume scaffval.k: |- K = ( Base ` F )
  assume scaffval.a: |- .xb = ( .sf ` W )
  assume scaffval.s: |- .x. = ( .s ` W )


  assert |- ( .x. Fn ( K X. B ) -> .xb = .x. )

  proof
    c.x
    cK
    cB
    cxp
    wfn
    #
    c.x
    vx
    vy
    cK
    cB
    vx
    cv
    vy
    cv
    c.x
    co
    cmpt2
    #
    c.xb
    @0
    c.x
    @1
    wceq
    vx
    vy
    cK
    cB
    c.x
    fnov
    biimpi
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
    syl6reqr
end
