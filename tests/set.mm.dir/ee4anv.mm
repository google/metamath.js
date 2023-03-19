include "wa.mm"
include "wex.mm"
include "excom.mm"
include "exbii.mm"
include "eeanv.mm"
include "2exbii.mm"
include "3bitri.mm"

theorem ee4anv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ph z
  disjoint ph w
  disjoint ps x
  disjoint ps y
  disjoint y z
  disjoint w x
  assert |- ( E. x E. y E. z E. w ( ph /\ ps ) <-> ( E. x E. y ph /\ E. z E. w ps ) )

  proof
    wph
    wps
    wa
    vw
    wex
    #
    vz
    wex
    vy
    wex
    #
    vx
    wex
    @0
    vy
    wex
    #
    vz
    wex
    #
    vx
    wex
    wph
    vy
    wex
    #
    wps
    vw
    wex
    #
    wa
    #
    vz
    wex
    vx
    wex
    @4
    vx
    wex
    @5
    vz
    wex
    wa
    @1
    @3
    vx
    @0
    vy
    vz
    excom
    exbii
    @2
    @6
    vx
    vz
    wph
    wps
    vy
    vw
    eeanv
    2exbii
    @4
    @5
    vx
    vz
    eeanv
    3bitri
end
