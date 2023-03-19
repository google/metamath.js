include "wex.mm"
include "nfe1.mm"
include "19.9.mm"

theorem bj-exexbiex
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x E. x ph <-> E. x ph )

  proof
    wph
    vx
    wex
    vx
    wph
    vx
    nfe1
    19.9
end
