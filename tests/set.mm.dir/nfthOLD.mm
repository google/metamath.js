include "hbth.mm"
include "nfiOLD.mm"

theorem nfthOLD
  let wph: wff ph
  let vx: setvar x
  assume nfthOLD.1: |- ph


  assert |- nfOLD x ph

  proof
    wph
    vx
    wph
    vx
    nfthOLD.1
    hbth
    nfiOLD
end
