include "wal.mm"
include "wi.mm"
include "axc11r.mm"
include "aecoms.mm"

theorem axc11
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y


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
    aecoms
end
