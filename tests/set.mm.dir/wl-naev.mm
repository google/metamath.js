include "weq.mm"
include "wal.mm"
include "aev.mm"
include "con3i.mm"

theorem wl-naev
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u v
  assert |- ( -. A. x x = y -> -. A. u u = v )

  proof
    vu
    vv
    weq
    vu
    wal
    vx
    vy
    weq
    vx
    wal
    vu
    vv
    vx
    vy
    vx
    aev
    con3i
end
