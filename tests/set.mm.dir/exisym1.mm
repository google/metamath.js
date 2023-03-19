include "wfal.mm"
include "wex.mm"
include "nfe1.mm"
include "falim.mm"
include "eximi.mm"
include "exlimi.mm"

theorem exisym1
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x E. x F. -> E. x ph )

  proof
    wfal
    vx
    wex
    wph
    vx
    wex
    vx
    wph
    vx
    nfe1
    wfal
    wph
    vx
    wph
    falim
    eximi
    exlimi
end
