include "clmod.mm"
include "wcel.mm"
include "crg.mm"
include "cgrp.mm"
include "lmodring.mm"
include "ringgrp.mm"
include "syl.mm"

theorem lmodfgrp
  let cF: class F
  let cW: class W
  let vq: setvar q
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  assume lmodring.1: |- F = ( Scalar ` W )


  assert |- ( W e. LMod -> F e. Grp )

  proof
    cW
    clmod
    wcel
    cF
    crg
    wcel
    cF
    cgrp
    wcel
    cF
    cW
    lmodring.1
    lmodring
    cF
    ringgrp
    syl
end
