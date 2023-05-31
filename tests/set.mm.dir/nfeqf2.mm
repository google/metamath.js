include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "wnf.mm"
include "exnal.mm"
include "nfnf1.mm"
include "wi.mm"
include "ax13lem2.mm"
include "ax13lem1.mm"
include "syld.mm"
include "df-nf.mm"
include "sylibr.mm"
include "exlimi.mm"
include "sylbir.mm"

theorem nfeqf2
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x z
  assert |- ( -. A. x x = y -> F/ x z = y )

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
    vz
    vy
    weq
    #
    vx
    wnf
    #
    @0
    vx
    exnal
    @1
    @3
    vx
    @2
    vx
    nfnf1
    @1
    @2
    vx
    wex
    #
    @2
    vx
    wal
    #
    wi
    @3
    @1
    @4
    @2
    @5
    vx
    vy
    vz
    ax13lem2
    vx
    vy
    vz
    ax13lem1
    syld
    @2
    vx
    df-nf
    sylibr
    exlimi
    sylbir
end
