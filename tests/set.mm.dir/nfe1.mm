include "wex.mm"
include "hbe1.mm"
include "nf5i.mm"

theorem nfe1
  param wph: wff ph
  param vx: setvar x


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
