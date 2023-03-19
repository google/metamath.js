include "wi.mm"
include "nfriOLD.mm"
include "nfrdOLD.mm"
include "hbim1OLD.mm"
include "nfiOLD.mm"

theorem nfim1OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfim1OLD.1: |- nfOLD x ph
  assume nfim1OLD.2: |- ( ph -> nfOLD x ps )


  assert |- nfOLD x ( ph -> ps )

  proof
    wph
    wps
    wi
    vx
    wph
    wps
    vx
    wph
    vx
    nfim1OLD.1
    nfriOLD
    wph
    wps
    vx
    nfim1OLD.2
    nfrdOLD
    hbim1OLD
    nfiOLD
end
