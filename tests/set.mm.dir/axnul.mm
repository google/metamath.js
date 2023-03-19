include "wel.mm"
include "wfal.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "wn.mm"
include "ax-sep.mm"
include "fal.mm"
include "intnan.mm"
include "id.mm"
include "mtbiri.mm"
include "alimi.mm"
include "eximii.mm"

theorem axnul
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- E. x A. y -. y e. x

  proof
    vy
    vx
    wel
    #
    vy
    vz
    wel
    #
    wfal
    wa
    #
    wb
    #
    vy
    wal
    @0
    wn
    #
    vy
    wal
    vx
    wfal
    vy
    vx
    vz
    ax-sep
    @3
    @4
    vy
    @3
    @0
    @2
    wfal
    @1
    fal
    intnan
    @3
    id
    mtbiri
    alimi
    eximii
end
