include "wi.mm"
include "wex.mm"
include "19.23OLD.mm"
include "mpgbi.mm"

theorem exlimiOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exlimiOLD.1: |- nfOLD x ps
  assume exlimiOLD.2: |- ( ph -> ps )


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
    exlimiOLD.1
    19.23OLD
    exlimiOLD.2
    mpgbi
end
