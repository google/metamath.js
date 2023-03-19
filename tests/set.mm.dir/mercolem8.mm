include "wi.mm"
include "wfal.mm"
include "merco2.mm"
include "mercolem3.mm"
include "ax-mp.mm"
include "mercolem7.mm"

theorem mercolem8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph -> ps ) -> ( ( ps -> ( ph -> ch ) ) -> ( ta -> ( th -> ( ph -> ch ) ) ) ) )

  proof
    wph
    wph
    wi
    #
    wfal
    wph
    wi
    #
    wph
    wi
    wi
    @0
    wph
    @0
    wi
    wi
    wi
    #
    wph
    wps
    wi
    #
    wps
    wph
    wch
    wi
    #
    wi
    wta
    wth
    @4
    wi
    wi
    wi
    #
    wi
    #
    wph
    wph
    wph
    wph
    wph
    wph
    merco2
    #
    @2
    @2
    @6
    wi
    #
    @7
    @4
    @1
    wps
    wi
    #
    wi
    @9
    wi
    #
    @6
    wi
    #
    @2
    @8
    wi
    #
    @10
    @5
    wi
    @11
    @4
    @9
    wph
    wps
    wta
    wth
    merco2
    @3
    @10
    @5
    mercolem3
    ax-mp
    @6
    @1
    @10
    wi
    #
    wi
    @13
    wi
    #
    @11
    @12
    wi
    @3
    @10
    wi
    @14
    wph
    wps
    wch
    @1
    mercolem7
    @3
    @10
    @5
    @1
    mercolem7
    ax-mp
    @6
    @13
    wph
    @10
    @2
    @2
    merco2
    ax-mp
    ax-mp
    ax-mp
    ax-mp
end
