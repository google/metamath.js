include "wi.mm"
include "wex.mm"
include "exim.mm"
include "mpg.mm"

theorem eximi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume eximi.1: |- ( ph -> ps )


  assert |- ( E. x ph -> E. x ps )

  proof
    wph
    wps
    wi
    wph
    vx
    wex
    wps
    vx
    wex
    wi
    vx
    wph
    wps
    vx
    exim
    eximi.1
    mpg
end
