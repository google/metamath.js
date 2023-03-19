include "weq.mm"
include "wal.mm"
include "axc16g.mm"
include "spsd.mm"

theorem axc11v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x x = y -> ( A. x ph -> A. y ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wph
    wph
    vy
    wal
    vx
    wph
    vx
    vy
    vy
    axc16g
    spsd
end
