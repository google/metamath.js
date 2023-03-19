include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "co.mm"
include "wceq.mm"
include "lmodgrp.mm"
include "grplid.mm"
include "sylan.mm"

theorem lmod0vlid
  let c.pl: class .+
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume 0vlid.v: |- V = ( Base ` W )
  assume 0vlid.a: |- .+ = ( +g ` W )
  assume 0vlid.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( .0. .+ X ) = X )

  proof
    cW
    clmod
    wcel
    cW
    cgrp
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
    lmodgrp
    cV
    c.pl
    cW
    cX
    c.0
    0vlid.v
    0vlid.a
    0vlid.z
    grplid
    sylan
end
