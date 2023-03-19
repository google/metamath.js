include "wa.mm"
include "wex.mm"
include "19.42v.mm"
include "exbii.mm"
include "19.41v.mm"
include "bitri.mm"

theorem bj-eeanvw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) )

  proof
    wph
    wps
    wa
    vy
    wex
    #
    vx
    wex
    wph
    wps
    vy
    wex
    #
    wa
    #
    vx
    wex
    wph
    vx
    wex
    @1
    wa
    @0
    @2
    vx
    wph
    wps
    vy
    19.42v
    exbii
    wph
    @1
    vx
    19.41v
    bitri
end
