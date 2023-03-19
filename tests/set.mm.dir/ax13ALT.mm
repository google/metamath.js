include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "sp.mm"
include "con3i.mm"
include "axc9.mm"
include "syl2im.mm"
include "ax13b.mm"
include "mpbir.mm"

theorem ax13ALT
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
    sp
    con3i
    @8
    @5
    @5
    vx
    sp
    con3i
    vy
    vz
    vx
    axc9
    syl2im
    @3
    vx
    vy
    vz
    ax13b
    mpbir
end
