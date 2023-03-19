include "ctrg.mm"
include "wcel.mm"
include "crg.mm"
include "cgrp.mm"
include "trgring.mm"
include "ringgrp.mm"
include "syl.mm"

theorem trggrp
  let cR: class R


  assert |- ( R e. TopRing -> R e. Grp )

  proof
    cR
    ctrg
    wcel
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    cR
    trgring
    cR
    ringgrp
    syl
end
