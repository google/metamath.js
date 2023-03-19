include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "eeanv.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "exbii.mm"
include "19.42v.mm"
include "bitri.mm"
include "2exbii.mm"
include "nfv.mm"
include "nfex.mm"
include "19.41.mm"
include "3bitri.mm"
include "3bitr4i.mm"

theorem eeeanv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint ph y
  disjoint ph z
  disjoint ps x
  disjoint ps z
  disjoint ch x
  disjoint ch y
  assert |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <-> ( E. x ph /\ E. y ps /\ E. z ch ) )

  proof
    wph
    wps
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wch
    vz
    wex
    #
    wa
    #
    wph
    vx
    wex
    #
    wps
    vy
    wex
    #
    wa
    #
    @3
    wa
    wph
    wps
    wch
    w3a
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    @5
    @6
    @3
    w3a
    @2
    @7
    @3
    wph
    wps
    vx
    vy
    eeanv
    anbi1i
    @10
    @0
    @3
    wa
    #
    vy
    wex
    #
    vx
    wex
    @1
    @3
    wa
    #
    vx
    wex
    @4
    @9
    @11
    vx
    vy
    @9
    @0
    wch
    wa
    #
    vz
    wex
    @11
    @8
    @14
    vz
    wph
    wps
    wch
    df-3an
    exbii
    @0
    wch
    vz
    19.42v
    bitri
    2exbii
    @12
    @13
    vx
    @0
    @3
    vy
    wch
    vy
    vz
    wch
    vy
    nfv
    nfex
    19.41
    exbii
    @1
    @3
    vx
    wch
    vx
    vz
    wch
    vx
    nfv
    nfex
    19.41
    3bitri
    @5
    @6
    @3
    df-3an
    3bitr4i
end
