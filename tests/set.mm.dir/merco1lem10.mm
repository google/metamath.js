include "wi.mm"
include "wfal.mm"
include "merco1.mm"
include "merco1lem2.mm"
include "ax-mp.mm"

theorem merco1lem10
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ( ph -> ps ) -> ch ) -> ( ta -> ch ) ) -> ph ) -> ( th -> ph ) )

  proof
    wph
    wps
    wi
    #
    wth
    wfal
    wi
    #
    wi
    wch
    wph
    wi
    wta
    wfal
    wi
    wi
    wph
    wi
    #
    wfal
    wi
    #
    wi
    @0
    wch
    wi
    wta
    wch
    wi
    wi
    #
    wi
    #
    @4
    wph
    wi
    wth
    wph
    wi
    wi
    @2
    @0
    wi
    @4
    wi
    @5
    wch
    wph
    wta
    wph
    @0
    merco1
    @2
    @0
    @4
    @1
    merco1lem2
    ax-mp
    wph
    wps
    wth
    @3
    @4
    merco1
    ax-mp
end
