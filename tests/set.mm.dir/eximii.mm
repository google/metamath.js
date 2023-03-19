include "wex.mm"
include "eximi.mm"
include "ax-mp.mm"

theorem eximii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume eximii.1: |- E. x ph
  assume eximii.2: |- ( ph -> ps )


  assert |- E. x ps

  proof
    wph
    vx
    wex
    wps
    vx
    wex
    eximii.1
    wph
    wps
    vx
    eximii.2
    eximi
    ax-mp
end
