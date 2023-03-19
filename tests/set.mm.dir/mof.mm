include "wfal.mm"
include "wex.mm"
include "wmo.mm"
include "nextf.mm"
include "exmo.mm"
include "mtpor.mm"

theorem mof
  let vx: setvar x


  assert |- E* x F.

  proof
    wfal
    vx
    wex
    wfal
    vx
    wmo
    vx
    nextf
    wfal
    vx
    exmo
    mtpor
end
