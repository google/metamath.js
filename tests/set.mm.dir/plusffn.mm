include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "plusffval.mm"
include "ovex.mm"
include "fnmpt2i.mm"

theorem plusffn
  let cB: class B
  let c.pd: class .+^
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  assume plusffn.1: |- B = ( Base ` G )
  assume plusffn.2: |- .+^ = ( +f ` G )


  assert |- .+^ Fn ( B X. B )

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
    cG
    cplusg
    cfv
    #
    co
    c.pd
    vx
    vy
    cB
    @2
    c.pd
    cG
    plusffn.1
    @2
    eqid
    plusffn.2
    plusffval
    @0
    @1
    @2
    ovex
    fnmpt2i
end
