include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-c9.mm"
include "pm2.43i.mm"
include "alimi.mm"
include "ax-c10.mm"
include "syl.mm"
include "ax-c7.mm"
include "pm2.61i.mm"

theorem equid1ALT
  let vx: setvar x


  assert |- x = x

  proof
    vx
    vx
    weq
    #
    vx
    wal
    #
    wn
    #
    vx
    wal
    #
    @0
    @3
    @0
    @1
    wi
    #
    vx
    wal
    @0
    @2
    @4
    vx
    @2
    @4
    vx
    vx
    vx
    ax-c9
    pm2.43i
    alimi
    @0
    vx
    vx
    ax-c10
    syl
    @0
    vx
    ax-c7
    pm2.61i
end
