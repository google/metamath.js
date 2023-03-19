include "wi.mm"
include "wfal.mm"
include "merco1.mm"
include "merco1lem4.mm"
include "ax-mp.mm"
include "merco1lem12.mm"

theorem merco1lem13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ( ( ph -> ps ) -> ( ch -> ps ) ) -> ta ) -> ( ph -> ta ) )

  proof
    wta
    wph
    wi
    #
    wph
    wfal
    wi
    wi
    wph
    wi
    wph
    wps
    wi
    wch
    wps
    wi
    wi
    #
    wi
    #
    @1
    wta
    wi
    wph
    wta
    wi
    wi
    wph
    @1
    wi
    #
    @2
    wps
    wph
    wi
    wch
    wfal
    wi
    wi
    wph
    wi
    #
    wph
    wi
    @1
    wi
    @3
    wps
    wph
    wch
    wph
    wph
    merco1
    @4
    wph
    @1
    merco1lem4
    ax-mp
    wph
    @1
    @0
    wfal
    merco1lem12
    ax-mp
    wta
    wph
    wph
    wph
    @1
    merco1
    ax-mp
end
