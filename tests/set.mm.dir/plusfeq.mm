include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "fnov.mm"
include "biimpi.mm"
include "plusffval.mm"
include "syl6reqr.mm"

theorem plusfeq
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cG: class G
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume plusffval.1: |- B = ( Base ` G )
  assume plusffval.2: |- .+ = ( +g ` G )
  assume plusffval.3: |- .+^ = ( +f ` G )


  assert |- ( .+ Fn ( B X. B ) -> .+^ = .+ )

  proof
    c.pl
    cB
    cB
    cxp
    wfn
    #
    c.pl
    vx
    vy
    cB
    cB
    vx
    cv
    vy
    cv
    c.pl
    co
    cmpt2
    #
    c.pd
    @0
    c.pl
    @1
    wceq
    vx
    vy
    cB
    cB
    c.pl
    fnov
    biimpi
    vx
    vy
    cB
    c.pl
    c.pd
    cG
    plusffval.1
    plusffval.2
    plusffval.3
    plusffval
    syl6reqr
end
