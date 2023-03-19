include "weq.mm"
include "wn.mm"
include "wal.mm"
include "equid.mm"
include "notnoti.mm"
include "spfalw.mm"
include "mt2.mm"

theorem ax6dgen
  let vx: setvar x


  assert |- -. A. x -. x = x

  proof
    vx
    vx
    weq
    #
    wn
    #
    vx
    wal
    @0
    vx
    equid
    #
    @1
    vx
    @0
    @2
    notnoti
    spfalw
    mt2
end
