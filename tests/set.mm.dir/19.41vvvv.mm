include "wa.mm"
include "wex.mm"
include "19.41vvv.mm"
include "exbii.mm"
include "19.41v.mm"
include "bitri.mm"

theorem 19.41vvvv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ps w
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( E. w E. x E. y E. z ( ph /\ ps ) <-> ( E. w E. x E. y E. z ph /\ ps ) )

  proof
    wph
    wps
    wa
    vz
    wex
    vy
    wex
    vx
    wex
    #
    vw
    wex
    wph
    vz
    wex
    vy
    wex
    vx
    wex
    #
    wps
    wa
    #
    vw
    wex
    @1
    vw
    wex
    wps
    wa
    @0
    @2
    vw
    wph
    wps
    vx
    vy
    vz
    19.41vvv
    exbii
    @1
    wps
    vw
    19.41v
    bitri
end
