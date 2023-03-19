include "wi.mm"
include "wex.mm"
include "19.37v.mm"
include "exbii.mm"
include "bitri.mm"

theorem 19.37vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ps x
  disjoint ps y
  assert |- ( E. x E. y ( ps -> ph ) <-> ( ps -> E. x E. y ph ) )

  proof
    wps
    wph
    wi
    vy
    wex
    #
    vx
    wex
    wps
    wph
    vy
    wex
    #
    wi
    #
    vx
    wex
    wps
    @1
    vx
    wex
    wi
    @0
    @2
    vx
    wps
    wph
    vy
    19.37v
    exbii
    wps
    @1
    vx
    19.37v
    bitri
end
