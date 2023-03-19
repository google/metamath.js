include "wi.mm"
include "wfal.mm"
include "merco1lem15.mm"
include "merco1lem11.mm"
include "ax-mp.mm"
include "merco1.mm"

theorem merco1lem16
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ( ph -> ( ps -> ch ) ) -> ta ) -> ( ( ph -> ch ) -> ta ) )

  proof
    wta
    wph
    wi
    #
    wph
    wch
    wi
    #
    wfal
    wi
    wi
    wfal
    wi
    wph
    wps
    wch
    wi
    wi
    #
    wi
    #
    @2
    wta
    wi
    @1
    wta
    wi
    wi
    @1
    @2
    wi
    @3
    wph
    wch
    wps
    merco1lem15
    @1
    @2
    @0
    wfal
    merco1lem11
    ax-mp
    wta
    wph
    @1
    wfal
    @2
    merco1
    ax-mp
end
