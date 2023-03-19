include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "ax-c10.mm"
include "ax-c7.mm"
include "con4i.mm"
include "mpg.mm"

theorem ax6fromc10
  let vx: setvar x
  let vy: setvar y


  assert |- -. A. x -. x = y

  proof
    vx
    vy
    weq
    #
    @0
    wn
    #
    vx
    wal
    wn
    #
    vx
    wal
    #
    wi
    @2
    vx
    @2
    vx
    vy
    ax-c10
    @3
    @0
    @1
    vx
    ax-c7
    con4i
    mpg
end
