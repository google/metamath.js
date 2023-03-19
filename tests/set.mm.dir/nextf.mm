include "wfal.mm"
include "fal.mm"
include "nex.mm"

theorem nextf
  let vx: setvar x


  assert |- -. E. x F.

  proof
    wfal
    vx
    fal
    nex
end
