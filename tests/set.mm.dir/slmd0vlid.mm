include "cslmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "co.mm"
include "wceq.mm"
include "slmdmnd.mm"
include "mndlid.mm"
include "sylan.mm"

theorem slmd0vlid
  let c.pl: class .+
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume slmd0vlid.v: |- V = ( Base ` W )
  assume slmd0vlid.a: |- .+ = ( +g ` W )
  assume slmd0vlid.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. SLMod /\ X e. V ) -> ( .0. .+ X ) = X )

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
    c.0
    cX
    c.pl
    co
    cX
    wceq
    cW
    slmdmnd
    cV
    c.pl
    cW
    cX
    c.0
    slmd0vlid.v
    slmd0vlid.a
    slmd0vlid.z
    mndlid
    sylan
end
