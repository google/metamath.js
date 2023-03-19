include "wex.mm"
include "wmo.mm"
include "nfe1.mm"
include "nfmo.mm"
include "19.8a.mm"
include "moimi.mm"
include "alrimi.mm"

theorem 2moex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E* x E. y ph -> A. y E* x ph )

  proof
    wph
    vy
    wex
    #
    vx
    wmo
    wph
    vx
    wmo
    vy
    @0
    vy
    vx
    wph
    vy
    nfe1
    nfmo
    wph
    @0
    vx
    wph
    vy
    19.8a
    moimi
    alrimi
end
