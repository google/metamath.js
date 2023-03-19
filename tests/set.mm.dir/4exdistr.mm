include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "19.42v.mm"
include "anbi2i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "3exbii.mm"
include "3exdistr.mm"
include "bitri.mm"

theorem 4exdistr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint ps z
  disjoint ps w
  disjoint ch w
  assert |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wth
    wa
    #
    wa
    vw
    wex
    #
    vz
    wex
    vy
    wex
    vx
    wex
    wph
    wps
    wch
    wth
    vw
    wex
    wa
    #
    w3a
    #
    vz
    wex
    vy
    wex
    vx
    wex
    wph
    wps
    @3
    vz
    wex
    wa
    vy
    wex
    wa
    vx
    wex
    @2
    @4
    vx
    vy
    vz
    @0
    @1
    vw
    wex
    #
    wa
    @0
    @3
    wa
    @2
    @4
    @5
    @3
    @0
    wch
    wth
    vw
    19.42v
    anbi2i
    @0
    @1
    vw
    19.42v
    wph
    wps
    @3
    df-3an
    3bitr4i
    3exbii
    wph
    wps
    @3
    vx
    vy
    vz
    3exdistr
    bitri
end
