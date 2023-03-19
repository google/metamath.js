include "wa.mm"
include "simpr.mm"
include "ax-mp.mm"

theorem simpri
  let wph: wff ph
  let wps: wff ps
  assume simpri.1: |- ( ph /\ ps )


  assert |- ps

  proof
    wph
    wps
    wa
    wps
    simpri.1
    wph
    wps
    simpr
    ax-mp
end
