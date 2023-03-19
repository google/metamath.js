include "wo.mm"
include "wal.mm"
include "pm10.12.mm"
include "alimi.mm"
include "syl.mm"

theorem pm11.12
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph x
  disjoint ph y
  assert |- ( A. x A. y ( ph \/ ps ) -> ( ph \/ A. x A. y ps ) )

  proof
    wph
    wps
    wo
    vy
    wal
    #
    vx
    wal
    wph
    wps
    vy
    wal
    #
    wo
    #
    vx
    wal
    wph
    @1
    vx
    wal
    wo
    @0
    @2
    vx
    wph
    wps
    vy
    pm10.12
    alimi
    wph
    @1
    vx
    pm10.12
    syl
end
