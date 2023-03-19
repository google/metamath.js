include "weq.mm"
include "wal.mm"
include "aevlem.mm"
include "alrimiv.mm"
include "syl.mm"

theorem hbaevg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w

  disjoint x y
  disjoint t u
  disjoint v z
  disjoint w z
  disjoint v w
  assert |- ( A. x x = y -> A. z A. t t = u )

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
    vt
    wal
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
    aevlem
    alrimiv
    syl
end
