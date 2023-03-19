include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wn.mm"
include "wal.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "ax-sep.mm"
include "id.mm"
include "biantru.mm"
include "bibi2i.mm"
include "biimpri.mm"
include "alimi.mm"
include "ax-ext.mm"
include "syl.mm"
include "eximi.mm"
include "ax-mp.mm"
include "df-ex.mm"
include "mpbi.mm"

theorem ax6vsep
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- -. A. x -. x = y

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    vx
    wex
    #
    @2
    wn
    vx
    wal
    wn
    vz
    cv
    #
    @0
    wcel
    #
    @4
    @1
    wcel
    #
    @4
    @4
    wceq
    #
    @7
    wi
    #
    wa
    #
    wb
    #
    vz
    wal
    #
    vx
    wex
    @3
    @8
    vz
    vx
    vy
    ax-sep
    @11
    @2
    vx
    @11
    @5
    @6
    wb
    #
    vz
    wal
    @2
    @10
    @12
    vz
    @12
    @10
    @6
    @9
    @5
    @8
    @6
    @7
    id
    biantru
    bibi2i
    biimpri
    alimi
    vx
    vy
    vz
    ax-ext
    syl
    eximi
    ax-mp
    @2
    vx
    df-ex
    mpbi
end
