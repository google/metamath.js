include "wa.mm"
include "wex.mm"
include "19.41v.mm"
include "exbii.mm"
include "bitri.mm"

theorem 19.41vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ps x
  disjoint ps y
  assert |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) )

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
    19.41v
    exbii
    @1
    wps
    vx
    19.41v
    bitri
end
