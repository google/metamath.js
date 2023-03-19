include "wex.mm"
include "hbe1.mm"
include "nf5i.mm"

theorem nfe1
  let wph: wff ph
  let vx: setvar x


  assert |- F/ x E. x ph

  proof
    wph
    vx
    wex
    vx
    wph
    vx
    hbe1
    nf5i
end
