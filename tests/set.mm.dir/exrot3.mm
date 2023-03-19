include "wex.mm"
include "excom13.mm"
include "excom.mm"
include "bitri.mm"

theorem exrot3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( E. x E. y E. z ph <-> E. y E. z E. x ph )

  proof
    wph
    vz
    wex
    vy
    wex
    vx
    wex
    wph
    vx
    wex
    #
    vy
    wex
    vz
    wex
    @0
    vz
    wex
    vy
    wex
    wph
    vx
    vy
    vz
    excom13
    @0
    vz
    vy
    excom
    bitri
end
