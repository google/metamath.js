include "wi.mm"
include "wex.mm"
include "19.23.mm"
include "mpgbi.mm"

theorem exlimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exlimi.1: |- F/ x ps
  assume exlimi.2: |- ( ph -> ps )


  assert |- ( E. x ph -> ps )

  proof
    wph
    wps
    wi
    wph
    vx
    wex
    wps
    wi
    vx
    wph
    wps
    vx
    exlimi.1
    19.23
    exlimi.2
    mpgbi
end
