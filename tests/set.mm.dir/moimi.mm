include "wi.mm"
include "wmo.mm"
include "moim.mm"
include "mpg.mm"

theorem moimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume moimi.1: |- ( ph -> ps )


  assert |- ( E* x ps -> E* x ph )

  proof
    wph
    wps
    wi
    wps
    vx
    wmo
    wph
    vx
    wmo
    wi
    vx
    wph
    wps
    vx
    moim
    moimi.1
    mpg
end
