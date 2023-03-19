include "cgic.mm"
include "cgim.mm"
include "cgrp.mm"
include "cxp.mm"
include "df-gic.mm"
include "gimfn.mm"
include "brwitnlem.mm"

theorem brgic
  let cR: class R
  let cS: class S


  assert |- ( R ~=g S <-> ( R GrpIso S ) =/= (/) )

  proof
    cR
    cS
    cgic
    cgim
    cgrp
    cgrp
    cxp
    df-gic
    gimfn
    brwitnlem
end
