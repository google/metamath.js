include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "nfanOLDOLD.mm"
include "nfxfrOLD.mm"

theorem nf3anOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfanOLDOLD.1: |- nfOLD x ph
  assume nfanOLDOLD.2: |- nfOLD x ps
  assume nfanOLD.3: |- nfOLD x ch


  assert |- nfOLD x ( ph /\ ps /\ ch )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    #
    wch
    wa
    vx
    wph
    wps
    wch
    df-3an
    @0
    wch
    vx
    wph
    wps
    vx
    nfanOLDOLD.1
    nfanOLDOLD.2
    nfanOLDOLD
    nfanOLD.3
    nfanOLDOLD
    nfxfrOLD
end
