include "wa.mm"
include "wex.mm"
include "excom.mm"
include "an32.mm"
include "2exbii.mm"
include "bitri.mm"
include "19.41v.mm"
include "exbii.mm"
include "3bitr3i.mm"

theorem pm11.6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y

  disjoint ps x
  disjoint ch y
  assert |- ( E. x ( E. y ( ph /\ ps ) /\ ch ) <-> E. y ( E. x ( ph /\ ch ) /\ ps ) )

  proof
    wph
    wps
    wa
    #
    wch
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wph
    wch
    wa
    #
    wps
    wa
    #
    vx
    wex
    #
    vy
    wex
    #
    @0
    vy
    wex
    wch
    wa
    #
    vx
    wex
    @4
    vx
    wex
    wps
    wa
    #
    vy
    wex
    @3
    @1
    vx
    wex
    vy
    wex
    @7
    @1
    vx
    vy
    excom
    @1
    @5
    vy
    vx
    wph
    wps
    wch
    an32
    2exbii
    bitri
    @2
    @8
    vx
    @0
    wch
    vy
    19.41v
    exbii
    @6
    @9
    vy
    @4
    wps
    vx
    19.41v
    exbii
    3bitr3i
end
