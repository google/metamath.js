include "cgrp.mm"
include "wcel.mm"
include "grpinvf.mm"
include "ffvelrnda.mm"

theorem grpinvcl
  let cB: class B
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpinvcl.b: |- B = ( Base ` G )
  assume grpinvcl.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( N ` X ) e. B )

  proof
    cG
    cgrp
    wcel
    cB
    cB
    cX
    cN
    cB
    cG
    cN
    grpinvcl.b
    grpinvcl.n
    grpinvf
    ffvelrnda
end
