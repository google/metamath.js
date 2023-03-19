include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "cfv.mm"
include "lmodgrp.mm"
include "grpinvcl.mm"
include "sylan.mm"

theorem lmodvnegcl
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lmodvnegcl.v: |- V = ( Base ` W )
  assume lmodvnegcl.n: |- N = ( invg ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( N ` X ) e. V )

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
    cN
    cfv
    cV
    wcel
    cW
    lmodgrp
    cV
    cW
    cN
    cX
    lmodvnegcl.v
    lmodvnegcl.n
    grpinvcl
    sylan
end
