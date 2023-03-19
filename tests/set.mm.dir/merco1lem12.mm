include "wi.mm"
include "wfal.mm"
include "merco1lem3.mm"
include "merco1.mm"
include "ax-mp.mm"
include "merco1lem9.mm"
include "merco1lem11.mm"

theorem merco1lem12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ph -> ps ) -> ( ( ( ch -> ( ph -> ta ) ) -> ph ) -> ps ) )

  proof
    wps
    wph
    wi
    #
    wch
    wph
    wta
    wi
    #
    wi
    #
    wph
    wi
    #
    wfal
    wi
    #
    wi
    wfal
    wi
    wph
    wi
    #
    wph
    wps
    wi
    @3
    wps
    wi
    wi
    @3
    wph
    wi
    #
    @5
    @3
    @6
    wi
    #
    @6
    @1
    @4
    wi
    wch
    wfal
    wi
    #
    wi
    @2
    wi
    @7
    @1
    @4
    wch
    merco1lem3
    wph
    wta
    @3
    @8
    @2
    merco1
    ax-mp
    @3
    wph
    merco1lem9
    ax-mp
    @3
    wph
    @0
    wfal
    merco1lem11
    ax-mp
    wps
    wph
    @3
    wfal
    wph
    merco1
    ax-mp
end
