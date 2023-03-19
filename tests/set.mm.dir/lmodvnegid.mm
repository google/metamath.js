include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "lmodgrp.mm"
include "grprinv.mm"
include "sylan.mm"

theorem lmodvnegid
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lmodvnegid.v: |- V = ( Base ` W )
  assume lmodvnegid.p: |- .+ = ( +g ` W )
  assume lmodvnegid.z: |- .0. = ( 0g ` W )
  assume lmodvnegid.n: |- N = ( invg ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( X .+ ( N ` X ) ) = .0. )

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
    cX
    cX
    cN
    cfv
    c.pl
    co
    c.0
    wceq
    cW
    lmodgrp
    cV
    c.pl
    cW
    cN
    cX
    c.0
    lmodvnegid.v
    lmodvnegid.p
    lmodvnegid.z
    lmodvnegid.n
    grprinv
    sylan
end
