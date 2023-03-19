include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "cgrp.mm"
include "drngring.mm"
include "ringgrp.mm"
include "syl.mm"

theorem drnggrp
  let cR: class R


  assert |- ( R e. DivRing -> R e. Grp )

  proof
    cR
    cdr
    wcel
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    cR
    drngring
    cR
    ringgrp
    syl
end
