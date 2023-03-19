include "weq.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "ax6ev.mm"
include "hbae.mm"
include "wi.mm"
include "ax7.mm"
include "sps.mm"
include "ancld.mm"
include "eximdh.mm"
include "mpi.mm"
include "axc4i.mm"
include "axc11.mm"
include "mpd.mm"
include "19.2.mm"
include "syl.mm"
include "excomim.mm"
include "equtrr.mm"
include "anim2d.mm"
include "2eximdv.mm"
include "syl5com.mm"

theorem ax6e2eq
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( A. x x = y -> ( u = v -> E. x E. y ( x = u /\ y = v ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    vx
    vu
    weq
    #
    vy
    vu
    weq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    vu
    vv
    weq
    #
    @2
    vy
    vv
    weq
    #
    wa
    #
    vy
    wex
    vx
    wex
    @1
    @4
    vx
    wex
    #
    vy
    wex
    #
    @5
    @1
    @9
    vy
    wal
    #
    @10
    @1
    @9
    vx
    wal
    @11
    @0
    @9
    vx
    @1
    @2
    vx
    wex
    @9
    vx
    vu
    ax6ev
    @1
    @2
    @4
    vx
    vx
    vy
    vx
    hbae
    @1
    @2
    @3
    @0
    @2
    @3
    wi
    vx
    vx
    vy
    vu
    ax7
    sps
    ancld
    eximdh
    mpi
    axc4i
    @9
    vx
    vy
    axc11
    mpd
    @9
    vy
    19.2
    syl
    @4
    vy
    vx
    excomim
    syl
    @6
    @4
    @8
    vx
    vy
    @6
    @3
    @7
    @2
    vu
    vv
    vy
    equtrr
    anim2d
    2eximdv
    syl5com
end
