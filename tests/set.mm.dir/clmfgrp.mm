include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "cgrp.mm"
include "clmlmod.mm"
include "lmodfgrp.mm"
include "syl.mm"

theorem clmfgrp
  let cF: class F
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )


  assert |- ( W e. CMod -> F e. Grp )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    cF
    cgrp
    wcel
    cW
    clmlmod
    cF
    cW
    clm0.f
    lmodfgrp
    syl
end
