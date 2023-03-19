include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmnd.mm"
include "ringgrp.mm"
include "grpmnd.mm"
include "syl.mm"

theorem ringmnd
  let cR: class R


  assert |- ( R e. Ring -> R e. Mnd )

  proof
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    cR
    cmnd
    wcel
    cR
    ringgrp
    cR
    grpmnd
    syl
end
