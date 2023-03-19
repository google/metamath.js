include "wnfOLD.mm"
include "a1i.mm"
include "nfan1OLD.mm"

theorem nfanOLDOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfanOLDOLD.1: |- nfOLD x ph
  assume nfanOLDOLD.2: |- nfOLD x ps


  assert |- nfOLD x ( ph /\ ps )

  proof
    wph
    wps
    vx
    nfanOLDOLD.1
    wps
    vx
    wnfOLD
    wph
    nfanOLDOLD.2
    a1i
    nfan1OLD
end
