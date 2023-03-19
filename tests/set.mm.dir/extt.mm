include "wtru.mm"
include "wal.mm"
include "wex.mm"
include "allt.mm"
include "19.2.mm"
include "ax-mp.mm"

theorem extt
  let vx: setvar x


  assert |- E. x T.

  proof
    wtru
    vx
    wal
    wtru
    vx
    wex
    vx
    allt
    wtru
    vx
    19.2
    ax-mp
end
