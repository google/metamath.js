include "co.mm"
include "ctpos.mm"
include "opprmulfval.mm"
include "oveqi.mm"
include "ovtpos.mm"
include "eqtri.mm"

theorem opprmul
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cO: class O
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume opprval.1: |- B = ( Base ` R )
  assume opprval.2: |- .x. = ( .r ` R )
  assume opprval.3: |- O = ( oppR ` R )
  assume opprmulfval.4: |- .xb = ( .r ` O )


  assert |- ( X .xb Y ) = ( Y .x. X )

  proof
    cX
    cY
    c.xb
    co
    cX
    cY
    c.x
    ctpos
    #
    co
    cY
    cX
    c.x
    co
    c.xb
    @0
    cX
    cY
    cB
    cR
    c.xb
    c.x
    cO
    opprval.1
    opprval.2
    opprval.3
    opprmulfval.4
    opprmulfval
    oveqi
    cX
    cY
    c.x
    ovtpos
    eqtri
end
