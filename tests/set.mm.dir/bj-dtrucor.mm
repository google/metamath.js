include "weq.mm"
include "cv.mm"
include "wne.mm"
include "wal.mm"
include "bj-dtru.mm"
include "pm2.21i.mm"
include "mpg.mm"

theorem bj-dtrucor
  let vx: setvar x
  let vy: setvar y
  assume bj-dtrucor.1: |- x = y

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
    bj-dtru
    pm2.21i
    bj-dtrucor.1
    mpg
end
