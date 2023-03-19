include "weq.mm"
include "wn.mm"
include "wal.mm"
include "ax6v.mm"
include "a1i.mm"

theorem bj-denot
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( x = x -> -. A. y -. y = x )

  proof
    vy
    vx
    weq
    wn
    vy
    wal
    wn
    vx
    vx
    weq
    vy
    vx
    ax6v
    a1i
end
