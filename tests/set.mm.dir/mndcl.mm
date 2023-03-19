include "cmnd.mm"
include "wcel.mm"
include "cmgm.mm"
include "co.mm"
include "mndmgm.mm"
include "mgmcl.mm"
include "syl3an1.mm"

theorem mndcl
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cZ: class Z
  assume mndcl.b: |- B = ( Base ` G )
  assume mndcl.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B )

  proof
    cG
    cmnd
    wcel
    cG
    cmgm
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.pl
    co
    cB
    wcel
    cG
    mndmgm
    cB
    cG
    cX
    cY
    c.pl
    mndcl.b
    mndcl.p
    mgmcl
    syl3an1
end
