include "wex.mm"
include "excom.mm"
include "biimpi.mm"

theorem excomim
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x E. y ph -> E. y E. x ph )

  proof
    wph
    vy
    wex
    vx
    wex
    wph
    vx
    wex
    vy
    wex
    wph
    vx
    vy
    excom
    biimpi
end
