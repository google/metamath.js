include "wfal.mm"
include "weu.mm"
include "wex.mm"
include "nextf.mm"
include "euex.mm"
include "mto.mm"

theorem unnf
  let vx: setvar x


  assert |- -. E! x F.

  proof
    wfal
    vx
    weu
    wfal
    vx
    wex
    vx
    nextf
    wfal
    vx
    euex
    mto
end
