include "wo.mm"
include "wex.mm"
include "19.43.mm"
include "bicomi.mm"

theorem pm10.42
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E. x ph \/ E. x ps ) <-> E. x ( ph \/ ps ) )

  proof
    wph
    wps
    wo
    vx
    wex
    wph
    vx
    wex
    wps
    vx
    wex
    wo
    wph
    wps
    vx
    19.43
    bicomi
end
