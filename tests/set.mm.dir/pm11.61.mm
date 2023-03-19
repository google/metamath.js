include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.12.mm"
include "19.37v.mm"
include "biimpi.mm"
include "alimi.mm"
include "syl.mm"

theorem pm11.61
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( E. y A. x ( ph -> ps ) -> A. x ( ph -> E. y ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    vy
    wex
    @0
    vy
    wex
    #
    vx
    wal
    wph
    wps
    vy
    wex
    wi
    #
    vx
    wal
    @0
    vy
    vx
    19.12
    @1
    @2
    vx
    @1
    @2
    wph
    wps
    vy
    19.37v
    biimpi
    alimi
    syl
end
