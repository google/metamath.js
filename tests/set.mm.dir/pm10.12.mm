include "wo.mm"
include "wal.mm"
include "19.32v.mm"
include "biimpi.mm"

theorem pm10.12
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( A. x ( ph \/ ps ) -> ( ph \/ A. x ps ) )

  proof
    wph
    wps
    wo
    vx
    wal
    wph
    wps
    vx
    wal
    wo
    wph
    wps
    vx
    19.32v
    biimpi
end
