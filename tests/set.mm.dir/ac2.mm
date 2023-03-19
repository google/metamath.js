include "wel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wreu.mm"
include "wral.mm"
include "wex.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "ax-ac.mm"
include "aceq0.mm"
include "mpbir.mm"

theorem ac2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint t w
  disjoint t v
  disjoint t u
  assert |- E. y A. z e. x A. w e. z E! v e. z E. u e. y ( z e. u /\ v e. u )

  proof
    vz
    vu
    wel
    vv
    vu
    wel
    wa
    vu
    vy
    cv
    wrex
    vv
    vz
    cv
    #
    wreu
    vw
    @0
    wral
    vz
    vx
    cv
    wral
    vy
    wex
    vz
    vw
    wel
    vw
    vx
    wel
    wa
    vu
    vw
    wel
    vw
    vt
    wel
    wa
    vu
    vt
    wel
    vt
    vy
    wel
    wa
    wa
    vt
    wex
    vu
    vv
    weq
    wb
    vu
    wal
    vv
    wex
    wi
    vw
    wal
    vz
    wal
    vy
    wex
    vx
    vy
    vz
    vw
    vv
    vu
    vt
    ax-ac
    vx
    vy
    vz
    vw
    vv
    vu
    vt
    aceq0
    mpbir
end
