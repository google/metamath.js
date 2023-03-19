include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "lmodgrp.mm"
include "grpass.mm"
include "sylan.mm"

theorem lmodass
  let c.pl: class .+
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lmodvacl.v: |- V = ( Base ` W )
  assume lmodvacl.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. LMod /\ ( X e. V /\ Y e. V /\ Z e. V ) ) -> ( ( X .+ Y ) .+ Z ) = ( X .+ ( Y .+ Z ) ) )

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
    lmodgrp
    cV
    c.pl
    cW
    cX
    cY
    cZ
    lmodvacl.v
    lmodvacl.a
    grpass
    sylan
end
