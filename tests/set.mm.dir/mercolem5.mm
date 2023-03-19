include "wi.mm"
include "wfal.mm"
include "merco2.mm"
include "mercolem1.mm"
include "ax-mp.mm"
include "mercolem2.mm"

theorem mercolem5
  let wph: wff ph
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) )

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
    wth
    wth
    wph
    wi
    wta
    wch
    wph
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
    @4
    wi
    #
    @5
    @1
    wth
    wi
    #
    @4
    wi
    #
    @2
    @6
    wi
    #
    @0
    @7
    wi
    @3
    wi
    @8
    wph
    wph
    wph
    wth
    wta
    wch
    merco2
    @0
    @7
    @3
    wth
    mercolem1
    ax-mp
    @4
    wth
    wi
    @1
    @7
    wi
    wi
    @8
    @9
    wi
    wth
    @3
    @1
    @1
    mercolem2
    @4
    wth
    wph
    @7
    @2
    @2
    merco2
    ax-mp
    ax-mp
    ax-mp
    ax-mp
end
