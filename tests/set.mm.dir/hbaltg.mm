include "wal.mm"
include "wi.mm"
include "alim.mm"
include "ax-11.mm"
include "syl6.mm"

theorem hbaltg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> A. y ps ) -> ( A. x ph -> A. y A. x ps ) )

  proof
    wph
    wps
    vy
    wal
    #
    wi
    vx
    wal
    wph
    vx
    wal
    @0
    vx
    wal
    wps
    vx
    wal
    vy
    wal
    wph
    @0
    vx
    alim
    wps
    vx
    vy
    ax-11
    syl6
end
