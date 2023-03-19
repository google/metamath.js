include "cmnd.mm"
include "wcel.mm"
include "csgrp.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "mndsgrp.mm"
include "sgrpass.mm"
include "sylan.mm"

theorem mndass
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mndcl.b: |- B = ( Base ` G )
  assume mndcl.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .+ Y ) .+ Z ) = ( X .+ ( Y .+ Z ) ) )

  proof
    cG
    cmnd
    wcel
    cG
    csgrp
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    cX
    cY
    cZ
    c.pl
    co
    c.pl
    co
    wceq
    cG
    mndsgrp
    cB
    cG
    cX
    cY
    c.pl
    cZ
    mndcl.b
    mndcl.p
    sgrpass
    sylan
end
