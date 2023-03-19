include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "ax-c5.mm"
include "con3i.mm"
include "ax-c9.mm"
include "syl2im.mm"
include "ax13b.mm"
include "mpbir.mm"

theorem ax13fromc9
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. x = y -> ( y = z -> A. x y = z ) )

  proof
    vx
    vy
    weq
    #
    wn
    #
    vy
    vz
    weq
    #
    @2
    vx
    wal
    #
    wi
    #
    wi
    @1
    vx
    vz
    weq
    #
    wn
    #
    @4
    wi
    wi
    @1
    @0
    vx
    wal
    #
    wn
    @6
    @5
    vx
    wal
    #
    wn
    @4
    @7
    @0
    @0
    vx
    ax-c5
    con3i
    @8
    @5
    @5
    vx
    ax-c5
    con3i
    vy
    vz
    vx
    ax-c9
    syl2im
    @3
    vx
    vy
    vz
    ax13b
    mpbir
end
