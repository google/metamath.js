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
include "aceq0.mm"
include "albii.mm"
include "bitri.mm"

theorem dfac0
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
  disjoint t x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint u v
  disjoint t v
  disjoint t u
  assert |- ( CHOICE <-> A. x E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) ) )

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
    @2
    vx
    vx
    vy
    vz
    vw
    vv
    vu
    vt
    aceq0
    albii
    bitri
end
