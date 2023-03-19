include "weq.mm"
include "wal.mm"
include "wn.mm"
include "aev.mm"
include "con3i.mm"
include "ax-5.mm"
include "alimi.mm"
include "3syl.mm"

theorem wl-hbnaev
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u

  disjoint x y
  disjoint t u
  disjoint u z
  disjoint t z
  assert |- ( -. A. x x = y -> A. z -. A. x x = y )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    wn
    #
    vu
    vt
    weq
    vu
    wal
    #
    wn
    #
    @3
    vz
    wal
    @1
    vz
    wal
    @2
    @0
    vu
    vt
    vx
    vy
    vx
    aev
    con3i
    @3
    vz
    ax-5
    @3
    @1
    vz
    @0
    @2
    vx
    vy
    vu
    vt
    vu
    aev
    con3i
    alimi
    3syl
end
