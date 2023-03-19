include "co.mm"
include "ctpos.mm"
include "oppgplusfval.mm"
include "oveqi.mm"
include "ovtpos.mm"
include "eqtri.mm"

theorem oppgplus
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cO: class O
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume oppgval.2: |- .+ = ( +g ` R )
  assume oppgval.3: |- O = ( oppG ` R )
  assume oppgplusfval.4: |- .+b = ( +g ` O )


  assert |- ( X .+b Y ) = ( Y .+ X )

  proof
    cX
    cY
    c.pb
    co
    cX
    cY
    c.pl
    ctpos
    #
    co
    cY
    cX
    c.pl
    co
    c.pb
    @0
    cX
    cY
    c.pl
    c.pb
    cR
    cO
    oppgval.2
    oppgval.3
    oppgplusfval.4
    oppgplusfval
    oveqi
    cX
    cY
    c.pl
    ovtpos
    eqtri
end
