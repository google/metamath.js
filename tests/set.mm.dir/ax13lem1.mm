include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "wal.mm"
include "equviniva.mm"
include "ax13v.mm"
include "equeucl.mm"
include "alimdv.mm"
include "syl9.mm"
include "impd.mm"
include "exlimdv.mm"
include "syl5.mm"

theorem ax13lem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w x
  disjoint w z
  disjoint w y
  assert |- ( -. x = y -> ( z = y -> A. x z = y ) )

  proof
    vz
    vy
    weq
    #
    vz
    vw
    weq
    #
    vy
    vw
    weq
    #
    wa
    #
    vw
    wex
    vx
    vy
    weq
    wn
    #
    @0
    vx
    wal
    #
    vz
    vy
    vw
    equviniva
    @4
    @3
    @5
    vw
    @4
    @1
    @2
    @5
    @4
    @2
    @2
    vx
    wal
    @1
    @5
    vx
    vy
    vw
    ax13v
    @1
    @2
    @0
    vx
    vz
    vy
    vw
    equeucl
    alimdv
    syl9
    impd
    exlimdv
    syl5
end
