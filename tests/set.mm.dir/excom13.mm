include "wex.mm"
include "excom.mm"
include "exbii.mm"
include "3bitri.mm"

theorem excom13
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( E. x E. y E. z ph <-> E. z E. y E. x ph )

  proof
    wph
    vz
    wex
    #
    vy
    wex
    vx
    wex
    @0
    vx
    wex
    #
    vy
    wex
    wph
    vx
    wex
    #
    vz
    wex
    #
    vy
    wex
    @2
    vy
    wex
    vz
    wex
    @0
    vx
    vy
    excom
    @1
    @3
    vy
    wph
    vx
    vz
    excom
    exbii
    @2
    vy
    vz
    excom
    3bitri
end
