include "weq.mm"
include "wal.mm"
include "axc16g.mm"
include "spsd.mm"

theorem axc11rv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x x = y -> ( A. y ph -> A. x ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wph
    wph
    vx
    wal
    vy
    wph
    vx
    vy
    vx
    axc16g
    spsd
end
