include "chf.mm"
include "wtr.mm"
include "wel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "dftr2.mm"
include "hfelhf.mm"
include "ax-gen.mm"
include "mpgbir.mm"

theorem hftr
  let vx: setvar x
  let vy: setvar y


  assert |- Tr Hf

  proof
    chf
    wtr
    vx
    vy
    wel
    vy
    cv
    #
    chf
    wcel
    wa
    vx
    cv
    #
    chf
    wcel
    wi
    #
    vy
    wal
    vx
    vx
    vy
    chf
    dftr2
    @2
    vy
    @1
    @0
    hfelhf
    ax-gen
    mpgbir
end
