include "wi.mm"
include "wfal.mm"
include "merco2.mm"
include "mercolem2.mm"
include "ax-mp.mm"

theorem mercolem3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps -> ch ) -> ( ps -> ( ph -> ch ) ) )

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
    wps
    wch
    wi
    #
    wps
    wph
    wch
    wi
    #
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
    wch
    wph
    wi
    #
    @1
    wps
    wi
    #
    wi
    #
    @6
    wi
    #
    @2
    @8
    wi
    #
    wch
    wph
    wph
    wps
    wps
    wph
    merco2
    @6
    @10
    wi
    @1
    @11
    wi
    wi
    #
    @12
    @13
    wi
    @10
    @5
    wi
    @1
    @6
    wi
    wi
    #
    @14
    @5
    wps
    wi
    @1
    @10
    wi
    wi
    @15
    wps
    @4
    @1
    @1
    mercolem2
    @5
    wps
    wph
    @10
    @1
    @3
    merco2
    ax-mp
    @10
    @5
    wph
    @6
    @1
    @9
    merco2
    ax-mp
    @6
    @10
    wph
    @11
    @2
    @2
    merco2
    ax-mp
    ax-mp
    ax-mp
    ax-mp
end
