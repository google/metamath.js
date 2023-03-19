include "wal.mm"
include "wi.mm"
include "axc11r.mm"
include "bj-aecomsv.mm"

theorem bj-axc11v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x x = y -> ( A. x ph -> A. y ph ) )

  proof
    wph
    vx
    wal
    wph
    vy
    wal
    wi
    vy
    vx
    wph
    vx
    vy
    axc11r
    bj-aecomsv
end
