include "w3a.mm"
include "wex.mm"
include "wa.mm"
include "3anass.mm"
include "2exbii.mm"
include "19.42vv.mm"
include "exdistr.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "exbii.mm"

theorem 3exdistr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint ph y
  disjoint ph z
  disjoint ps z
  assert |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <-> E. x ( ph /\ E. y ( ps /\ E. z ch ) ) )

  proof
    wph
    wps
    wch
    w3a
    #
    vz
    wex
    vy
    wex
    #
    wph
    wps
    wch
    vz
    wex
    wa
    vy
    wex
    #
    wa
    #
    vx
    @1
    wph
    wps
    wch
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    wph
    @4
    vz
    wex
    vy
    wex
    #
    wa
    @3
    @0
    @5
    vy
    vz
    wph
    wps
    wch
    3anass
    2exbii
    wph
    @4
    vy
    vz
    19.42vv
    @6
    @2
    wph
    wps
    wch
    vy
    vz
    exdistr
    anbi2i
    3bitri
    exbii
end
