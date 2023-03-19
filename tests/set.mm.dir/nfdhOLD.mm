include "nfiOLD.mm"
include "nfdOLD.mm"

theorem nfdhOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfdhOLD.1: |- ( ph -> A. x ph )
  assume nfdhOLD.2: |- ( ph -> ( ps -> A. x ps ) )


  assert |- ( ph -> nfOLD x ps )

  proof
    wph
    wps
    vx
    wph
    vx
    nfdhOLD.1
    nfiOLD
    nfdhOLD.2
    nfdOLD
end
