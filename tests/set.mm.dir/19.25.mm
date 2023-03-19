include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "biimpi.mm"
include "aleximi.mm"

theorem 19.25
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. y E. x ( ph -> ps ) -> ( E. y A. x ph -> E. y E. x ps ) )

  proof
    wph
    wps
    wi
    vx
    wex
    #
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    vy
    @0
    @1
    @2
    wi
    wph
    wps
    vx
    19.35
    biimpi
    aleximi
end
