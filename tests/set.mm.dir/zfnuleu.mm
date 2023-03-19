include "wel.mm"
include "wn.mm"
include "wal.mm"
include "weu.mm"
include "wfal.mm"
include "wb.mm"
include "wex.mm"
include "nbfal.mm"
include "albii.mm"
include "exbii.mm"
include "mpbi.mm"
include "nfv.mm"
include "bm1.1.mm"
include "ax-mp.mm"
include "eubii.mm"
include "mpbir.mm"

theorem zfnuleu
  let vx: setvar x
  let vy: setvar y
  assume zfnuleu.1: |- E. x A. y -. y e. x

  disjoint x y
  assert |- E! x A. y -. y e. x

  proof
    vy
    vx
    wel
    #
    wn
    #
    vy
    wal
    #
    vx
    weu
    @0
    wfal
    wb
    #
    vy
    wal
    #
    vx
    weu
    #
    @4
    vx
    wex
    #
    @5
    @2
    vx
    wex
    @6
    zfnuleu.1
    @2
    @4
    vx
    @1
    @3
    vy
    @0
    nbfal
    albii
    #
    exbii
    mpbi
    wfal
    vx
    vy
    wfal
    vx
    nfv
    bm1.1
    ax-mp
    @2
    @4
    vx
    @7
    eubii
    mpbir
end
