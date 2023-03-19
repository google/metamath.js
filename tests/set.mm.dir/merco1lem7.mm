include "wi.mm"
include "wfal.mm"
include "merco1lem5.mm"
include "merco1.mm"
include "ax-mp.mm"
include "merco1lem6.mm"

theorem merco1lem7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ( ( ps -> ch ) -> ps ) -> ps ) )

  proof
    wps
    wch
    wi
    #
    wps
    wi
    #
    @1
    wps
    wi
    #
    wi
    #
    wph
    @2
    wi
    wps
    wfal
    wi
    @1
    wfal
    wi
    #
    wi
    wch
    wi
    @0
    wi
    @3
    wps
    @4
    wch
    merco1lem5
    wps
    wfal
    @1
    wch
    @0
    merco1
    ax-mp
    @1
    wps
    wph
    merco1lem6
    ax-mp
end
