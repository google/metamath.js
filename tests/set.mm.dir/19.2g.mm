include "wex.mm"
include "19.8a.mm"
include "sps.mm"

theorem 19.2g
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ph -> E. y ph )

  proof
    wph
    wph
    vy
    wex
    vx
    wph
    vy
    19.8a
    sps
end
