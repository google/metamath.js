include "wo.mm"
include "wn.mm"
include "wi.mm"
include "df-or.mm"
include "nfnOLD.mm"
include "nfimOLD.mm"
include "nfxfrOLD.mm"

theorem nforOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfOLD.1: |- nfOLD x ph
  assume nfOLD.2: |- nfOLD x ps


  assert |- nfOLD x ( ph \/ ps )

  proof
    wph
    wps
    wo
    wph
    wn
    #
    wps
    wi
    vx
    wph
    wps
    df-or
    @0
    wps
    vx
    wph
    vx
    nfOLD.1
    nfnOLD
    nfOLD.2
    nfimOLD
    nfxfrOLD
end
