include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "equvinv.mm"
include "ax13lem1.mm"
include "imp.mm"
include "ax7v1.mm"
include "alanimi.mm"
include "syl2an.mm"
include "an4s.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ax13b.mm"
include "mpbir.mm"

theorem ax13
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  let vw: setvar w


  assert |- ( -. x = y -> ( y = z -> A. x y = z ) )

  proof
    vx
    vy
    weq
    wn
    #
    vy
    vz
    weq
    #
    @1
    vx
    wal
    #
    wi
    #
    wi
    @0
    vx
    vz
    weq
    wn
    #
    @3
    wi
    wi
    @0
    @4
    @3
    @1
    vw
    vy
    weq
    #
    vw
    vz
    weq
    #
    wa
    #
    vw
    wex
    @0
    @4
    wa
    #
    @2
    vy
    vz
    vw
    equvinv
    @8
    @7
    @2
    vw
    @8
    @7
    @2
    @0
    @5
    @4
    @6
    @2
    @0
    @5
    wa
    @5
    vx
    wal
    #
    @6
    vx
    wal
    #
    @2
    @4
    @6
    wa
    @0
    @5
    @9
    vx
    vy
    vw
    ax13lem1
    imp
    @4
    @6
    @10
    vx
    vz
    vw
    ax13lem1
    imp
    @5
    @6
    @1
    vx
    @5
    @6
    @1
    vw
    vy
    vz
    ax7v1
    imp
    alanimi
    syl2an
    an4s
    ex
    exlimdv
    syl5bi
    ex
    @2
    vx
    vy
    vz
    ax13b
    mpbir
end
