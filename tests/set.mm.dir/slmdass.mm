include "cslmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "slmdmnd.mm"
include "mndass.mm"
include "sylan.mm"

theorem slmdass
  let c.pl: class .+
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume slmdvacl.v: |- V = ( Base ` W )
  assume slmdvacl.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. SLMod /\ ( X e. V /\ Y e. V /\ Z e. V ) ) -> ( ( X .+ Y ) .+ Z ) = ( X .+ ( Y .+ Z ) ) )

  proof
    cW
    cslmd
    wcel
    cW
    cmnd
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    cZ
    cV
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
    cW
    slmdmnd
    cV
    c.pl
    cW
    cX
    cY
    cZ
    slmdvacl.v
    slmdvacl.a
    mndass
    sylan
end
