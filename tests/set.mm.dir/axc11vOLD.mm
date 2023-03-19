include "weq.mm"
include "wal.mm"
include "wi.mm"
include "aevlem.mm"
include "axc11rv.mm"
include "syl.mm"

theorem axc11vOLD
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
    vy
    vx
    weq
    vy
    wal
    wph
    vx
    wal
    wph
    vy
    wal
    wi
    vx
    vy
    vy
    vx
    aevlem
    wph
    vy
    vx
    axc11rv
    syl
end
