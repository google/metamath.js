include "wa.mm"
include "wex.mm"
include "19.42vv.mm"
include "exbii.mm"
include "19.42v.mm"
include "bitri.mm"

theorem 19.42vvv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( E. x E. y E. z ( ph /\ ps ) <-> ( ph /\ E. x E. y E. z ps ) )

  proof
    wph
    wps
    wa
    vz
    wex
    vy
    wex
    #
    vx
    wex
    wph
    wps
    vz
    wex
    vy
    wex
    #
    wa
    #
    vx
    wex
    wph
    @1
    vx
    wex
    wa
    @0
    @2
    vx
    wph
    wps
    vy
    vz
    19.42vv
    exbii
    wph
    @1
    vx
    19.42v
    bitri
end
