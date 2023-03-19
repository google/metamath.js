include "cv.mm"
include "co.mm"
include "oveq12.mm"
include "plusffval.mm"
include "ovex.mm"
include "ovmpt2a.mm"

theorem plusfval
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cG: class G
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume plusffval.1: |- B = ( Base ` G )
  assume plusffval.2: |- .+ = ( +g ` G )
  assume plusffval.3: |- .+^ = ( +f ` G )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .+^ Y ) = ( X .+ Y ) )

  proof
    vx
    vy
    cX
    cY
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    cX
    cY
    c.pl
    co
    c.pd
    @0
    cX
    @1
    cY
    c.pl
    oveq12
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
    cX
    cY
    c.pl
    ovex
    ovmpt2a
end
