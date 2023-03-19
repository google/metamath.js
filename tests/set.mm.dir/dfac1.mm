include "wac.mm"
include "wel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wreu.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "weq.mm"
include "wb.mm"
include "wi.mm"
include "dfac7.mm"
include "aceq1.mm"
include "albii.mm"
include "bitri.mm"

theorem dfac1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint u x
  disjoint v y
  disjoint u y
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  assert |- ( CHOICE <-> A. x E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. x A. z ( E. x ( ( z e. w /\ w e. x ) /\ ( z e. x /\ x e. y ) ) <-> z = x ) ) )

  proof
    wac
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
    #
    vx
    wal
    vz
    vw
    wel
    vw
    vx
    wel
    wa
    #
    @2
    vz
    vx
    wel
    vx
    vy
    wel
    wa
    wa
    vx
    wex
    vz
    vx
    weq
    wb
    vz
    wal
    vx
    wex
    wi
    vw
    wal
    vz
    wal
    vy
    wex
    #
    vx
    wal
    vx
    vy
    vz
    vw
    vv
    vu
    dfac7
    @1
    @3
    vx
    vx
    vy
    vz
    vw
    vv
    vu
    aceq1
    albii
    bitri
end
