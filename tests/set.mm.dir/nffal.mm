include "wfal.mm"
include "fal.mm"
include "nfnth.mm"

theorem nffal
  let vx: setvar x


  assert |- F/ x F.

  proof
    wfal
    vx
    fal
    nfnth
end
