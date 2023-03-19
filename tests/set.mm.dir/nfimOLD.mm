include "wnfOLD.mm"
include "a1i.mm"
include "nfim1OLD.mm"

theorem nfimOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfimOLD.1: |- nfOLD x ph
  assume nfimOLD.2: |- nfOLD x ps


  assert |- nfOLD x ( ph -> ps )

  proof
    wph
    wps
    vx
    nfimOLD.1
    wps
    vx
    wnfOLD
    wph
    nfimOLD.2
    a1i
    nfim1OLD
end
