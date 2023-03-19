include "wa.mm"
include "wex.mm"
include "simpri.mm"
include "nfth.mm"
include "19.41.mm"
include "mpbir.mm"

theorem exanOLDOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exanOLDOLD.1: |- ( E. x ph /\ ps )


  assert |- E. x ( ph /\ ps )

  proof
    wph
    wps
    wa
    vx
    wex
    wph
    vx
    wex
    #
    wps
    wa
    exanOLDOLD.1
    wph
    wps
    vx
    wps
    vx
    @0
    wps
    exanOLDOLD.1
    simpri
    nfth
    19.41
    mpbir
end
