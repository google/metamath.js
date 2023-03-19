include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "lmodgrp.mm"
include "grplcan.mm"
include "sylan.mm"

theorem lmodlcan
  let c.pl: class .+
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lmodvacl.v: |- V = ( Base ` W )
  assume lmodvacl.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. LMod /\ ( X e. V /\ Y e. V /\ Z e. V ) ) -> ( ( Z .+ X ) = ( Z .+ Y ) <-> X = Y ) )

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
    cZ
    cX
    c.pl
    co
    cZ
    cY
    c.pl
    co
    wceq
    cX
    cY
    wceq
    wb
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
    grplcan
    sylan
end
