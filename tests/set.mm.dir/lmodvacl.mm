include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "co.mm"
include "lmodgrp.mm"
include "grpcl.mm"
include "syl3an1.mm"

theorem lmodvacl
  let c.pl: class .+
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lmodvacl.v: |- V = ( Base ` W )
  assume lmodvacl.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. LMod /\ X e. V /\ Y e. V ) -> ( X .+ Y ) e. V )

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
    cX
    cY
    c.pl
    co
    cV
    wcel
    cW
    lmodgrp
    cV
    c.pl
    cW
    cX
    cY
    lmodvacl.v
    lmodvacl.a
    grpcl
    syl3an1
end
