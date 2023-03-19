include "wex.mm"
include "hbe1.mm"
include "nfiOLD.mm"

theorem nfe1OLD
  let wph: wff ph
  let vx: setvar x


  assert |- nfOLD x E. x ph

  proof
    wph
    vx
    wex
    vx
    wph
    vx
    hbe1
    nfiOLD
end
