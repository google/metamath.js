include "weq.mm"
include "cv.mm"
include "wne.mm"
include "wal.mm"
include "dtru.mm"
include "pm2.21i.mm"
include "mpg.mm"

theorem dtrucor
  let vx: setvar x
  let vy: setvar y
  assume dtrucor.1: |- x = y

  disjoint x y
  assert |- x =/= y

  proof
    vx
    vy
    weq
    #
    vx
    cv
    vy
    cv
    wne
    #
    vx
    @0
    vx
    wal
    @1
    vx
    vy
    dtru
    pm2.21i
    dtrucor.1
    mpg
end
