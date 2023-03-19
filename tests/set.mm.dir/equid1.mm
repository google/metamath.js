include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-c4.mm"
include "ax-c5.mm"
include "ax-c9.mm"
include "sylc.mm"
include "mpg.mm"
include "ax-c10.mm"
include "syl.mm"
include "ax-c7.mm"
include "pm2.61i.mm"

theorem equid1
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
    #
    @0
    @3
    @4
    wi
    @3
    @5
    wi
    vx
    @2
    @4
    vx
    ax-c4
    @3
    @2
    @2
    @4
    @2
    vx
    ax-c5
    #
    @6
    vx
    vx
    vx
    ax-c9
    sylc
    mpg
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
