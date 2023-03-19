include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "wi.mm"
include "exnal.mm"
include "hbe1.mm"
include "ax13lem2.mm"
include "ax13lem1.mm"
include "syldc.mm"
include "aleximi.mm"
include "com12.mm"
include "hbe1a.mm"
include "syl56.mm"
include "sylbir.mm"

theorem wl-dveeq12
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( -. A. x x = y -> ( E. x z = y -> A. x z = y ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    @0
    wn
    #
    vx
    wex
    #
    vz
    vy
    weq
    #
    vx
    wex
    #
    @3
    vx
    wal
    #
    wi
    @0
    vx
    exnal
    @4
    @4
    vx
    wal
    #
    @2
    @5
    vx
    wex
    #
    @5
    @3
    vx
    hbe1
    @6
    @2
    @7
    @4
    @1
    @5
    vx
    @1
    @4
    @3
    @5
    vx
    vy
    vz
    ax13lem2
    vx
    vy
    vz
    ax13lem1
    syldc
    aleximi
    com12
    @3
    vx
    hbe1a
    syl56
    sylbir
end
