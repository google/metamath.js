include "wnfOLD.mm"
include "nfbiiOLD.mm"
include "mpbir.mm"

theorem nfxfrOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfbiiOLD.1: |- ( ph <-> ps )
  assume nfxfrOLD.2: |- nfOLD x ps


  assert |- nfOLD x ph

  proof
    wph
    vx
    wnfOLD
    wps
    vx
    wnfOLD
    nfxfrOLD.2
    wph
    wps
    vx
    nfbiiOLD.1
    nfbiiOLD
    mpbir
end
