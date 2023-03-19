include "wi.mm"
include "wfal.mm"
include "retbwax2.mm"
include "merco1.mm"
include "ax-mp.mm"

theorem merco1lem2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ( ph -> ps ) -> ch ) -> ( ( ( ps -> ta ) -> ( ph -> F. ) ) -> ch ) )

  proof
    wch
    wph
    wi
    #
    wps
    wta
    wi
    wph
    wfal
    wi
    wi
    #
    wfal
    wi
    #
    wi
    #
    wps
    wi
    wph
    wps
    wi
    #
    wi
    #
    @4
    wch
    wi
    @1
    wch
    wi
    wi
    @2
    @3
    wi
    @5
    @2
    @0
    retbwax2
    wps
    wta
    wph
    wfal
    @3
    merco1
    ax-mp
    wch
    wph
    @1
    wps
    @4
    merco1
    ax-mp
end
