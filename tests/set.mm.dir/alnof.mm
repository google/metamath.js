include "wfal.mm"
include "wn.mm"
include "fal.mm"
include "ax-gen.mm"

theorem alnof
  let vx: setvar x


  assert |- A. x -. F.

  proof
    wfal
    wn
    vx
    fal
    ax-gen
end
