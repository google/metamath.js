include "weq.mm"
include "wal.mm"
include "aev.mm"
include "alrimiv.mm"
include "syl.mm"

theorem aev2ALT
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let v.vs: setvar s
  let vw: setvar w

  disjoint x y
  disjoint s w
  disjoint w z
  disjoint s z
  assert |- ( A. x x = y -> A. z A. t u = v )

  proof
    vx
    vy
    weq
    vx
    wal
    vw
    v.vs
    weq
    vw
    wal
    #
    vu
    vv
    weq
    vt
    wal
    #
    vz
    wal
    vx
    vy
    vw
    v.vs
    vw
    aev
    @0
    @1
    vz
    vw
    v.vs
    vt
    vv
    vu
    aev
    alrimiv
    syl
end
