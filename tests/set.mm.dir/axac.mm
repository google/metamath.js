include "wel.mm"
include "wa.mm"
include "wex.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wac.mm"
include "axac3.mm"
include "dfac0.mm"
include "mpbi.mm"
include "spi.mm"

theorem axac
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
  assert |- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) )

  proof
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
    wac
    @0
    vx
    wal
    axac3
    vx
    vy
    vz
    vw
    vv
    vu
    vt
    dfac0
    mpbi
    spi
end
