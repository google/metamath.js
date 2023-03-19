include "wex.mm"
include "excom13.mm"
include "exbii.mm"
include "bitri.mm"

theorem exrot4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph )

  proof
    wph
    vw
    wex
    vz
    wex
    vy
    wex
    #
    vx
    wex
    wph
    vy
    wex
    #
    vz
    wex
    vw
    wex
    #
    vx
    wex
    @1
    vx
    wex
    vw
    wex
    vz
    wex
    @0
    @2
    vx
    wph
    vy
    vz
    vw
    excom13
    exbii
    @1
    vx
    vw
    vz
    excom13
    bitri
end
