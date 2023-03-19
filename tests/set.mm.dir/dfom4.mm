include "cv.mm"
include "wlim.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "com.mm"
include "elom3.mm"
include "abbi2i.mm"

theorem dfom4
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- _om = { x | A. y ( Lim y -> x e. y ) }

  proof
    vy
    cv
    wlim
    vx
    vy
    wel
    wi
    vy
    wal
    vx
    com
    vy
    vx
    cv
    elom3
    abbi2i
end
