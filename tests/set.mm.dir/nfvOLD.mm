include "ax-5.mm"
include "nfiOLD.mm"

theorem nfvOLD
  let wph: wff ph
  let vx: setvar x

  disjoint ph x
  assert |- nfOLD x ph

  proof
    wph
    vx
    wph
    vx
    ax-5
    nfiOLD
end
