include "cslmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "co.mm"
include "slmdmnd.mm"
include "mndcl.mm"
include "syl3an1.mm"

theorem slmdvacl
  let c.pl: class .+
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume slmdvacl.v: |- V = ( Base ` W )
  assume slmdvacl.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. SLMod /\ X e. V /\ Y e. V ) -> ( X .+ Y ) e. V )

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
    cX
    cY
    c.pl
    co
    cV
    wcel
    cW
    slmdmnd
    cV
    c.pl
    cW
    cX
    cY
    slmdvacl.v
    slmdvacl.a
    mndcl
    syl3an1
end
