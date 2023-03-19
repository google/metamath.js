include "c0.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wel.mm"
include "wn.mm"
include "wal.mm"
include "ax-nul.mm"
include "eq0.mm"
include "exbii.mm"
include "mpbir.mm"
include "issetri.mm"

theorem 0ex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- (/) e. _V

  proof
    vx
    c0
    vx
    cv
    #
    c0
    wceq
    #
    vx
    wex
    vy
    vx
    wel
    wn
    vy
    wal
    #
    vx
    wex
    vx
    vy
    ax-nul
    @1
    @2
    vx
    vy
    @0
    eq0
    exbii
    mpbir
    issetri
end
