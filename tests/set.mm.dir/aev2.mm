include "weq.mm"
include "wal.mm"
include "hbaevg.mm"
include "aev.mm"
include "sylg.mm"

theorem aev2
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
    vu
    vv
    weq
    vt
    wal
    vz
    vx
    vy
    vz
    v.vs
    vw
    hbaevg
    vw
    v.vs
    vt
    vv
    vu
    aev
    sylg
end
