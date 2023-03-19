include "cv.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "homffval.mm"
include "ovex.mm"
include "fnmpt2i.mm"

theorem homffn
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume homffn.f: |- F = ( Homf ` C )
  assume homffn.b: |- B = ( Base ` C )


  assert |- F Fn ( B X. B )

  proof
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cC
    chom
    cfv
    #
    co
    cF
    vx
    vy
    cB
    cC
    cF
    @2
    homffn.f
    homffn.b
    @2
    eqid
    homffval
    @0
    @1
    @2
    ovex
    fnmpt2i
end
