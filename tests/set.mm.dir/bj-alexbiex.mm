include "wex.mm"
include "nfe1.mm"
include "19.3.mm"

theorem bj-alexbiex
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x E. x ph <-> E. x ph )

  proof
    wph
    vx
    wex
    vx
    wph
    vx
    nfe1
    19.3
end
