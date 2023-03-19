include "wa.mm"
include "wex.mm"
include "19.41vv.mm"
include "exbii.mm"
include "19.41v.mm"
include "bitri.mm"

theorem 19.41vvv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( E. x E. y E. z ( ph /\ ps ) <-> ( E. x E. y E. z ph /\ ps ) )

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
    vz
    wex
    vy
    wex
    #
    wps
    wa
    #
    vx
    wex
    @1
    vx
    wex
    wps
    wa
    @0
    @2
    vx
    wph
    wps
    vy
    vz
    19.41vv
    exbii
    @1
    wps
    vx
    19.41v
    bitri
end
