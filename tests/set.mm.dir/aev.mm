include "weq.mm"
include "wal.mm"
include "aevlem.mm"
include "aeveq.mm"
include "alrimiv.mm"
include "syl.mm"

theorem aev
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w

  disjoint x y
  disjoint v w
  disjoint v z
  disjoint w z
  assert |- ( A. x x = y -> A. z t = u )

  proof
    vx
    vy
    weq
    vx
    wal
    vv
    vw
    weq
    vv
    wal
    #
    vt
    vu
    weq
    #
    vz
    wal
    vx
    vy
    vv
    vw
    aevlem
    @0
    @1
    vz
    vv
    vw
    vt
    vu
    aeveq
    alrimiv
    syl
end
