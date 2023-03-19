include "weq.mm"
include "wal.mm"
include "wi.mm"
include "dtru.mm"
include "pm2.21i.mm"

theorem axc16b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x x = y -> ( ph -> A. x ph ) )

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
    wi
    vx
    vy
    dtru
    pm2.21i
end
