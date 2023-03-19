include "wtru.mm"
include "wn.mm"
include "tru.mm"
include "notnoti.mm"
include "nex.mm"

theorem nextnt
  let vx: setvar x


  assert |- -. E. x -. T.

  proof
    wtru
    wn
    vx
    wtru
    tru
    notnoti
    nex
end
