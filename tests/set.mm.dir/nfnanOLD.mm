include "wnan.mm"
include "wa.mm"
include "wn.mm"
include "df-nan.mm"
include "nfanOLDOLD.mm"
include "nfnOLD.mm"
include "nfxfrOLD.mm"

theorem nfnanOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfanOLDOLD.1: |- nfOLD x ph
  assume nfanOLDOLD.2: |- nfOLD x ps


  assert |- nfOLD x ( ph -/\ ps )

  proof
    wph
    wps
    wnan
    wph
    wps
    wa
    #
    wn
    vx
    wph
    wps
    df-nan
    @0
    vx
    wph
    wps
    vx
    nfanOLDOLD.1
    nfanOLDOLD.2
    nfanOLDOLD
    nfnOLD
    nfxfrOLD
end
